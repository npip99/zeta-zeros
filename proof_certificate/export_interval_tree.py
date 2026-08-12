#!/usr/bin/env python3
"""Export compact proof trees for ``Zeta23Ext.VerifiedCertificate``.

This is deliberately separate from :mod:`zeta_ext.verify_general`; it does not
change the production verifier.  It specifies the proof-producing artifact
format and validates structural coverage before writing anything.

Binary format (preorder):

* header ``b"Z23TREE1"``;
* one byte for the dimension ``q`` and an unsigned 32-bit root count;
* unsigned 64-bit big-endian node count;
* one byte per node: ``0`` is a leaf, ``1..q`` is a split coordinate plus one.

Thus the committed 1,739,356-node search needs only about 1.66 MiB for its
entire subdivision topology.  Kernel-table entries and leaf lower-bound data
are separate artifacts because they have a distinct transcendental trust
boundary in Lean.

The ``from-events`` command accepts newline-delimited JSON records with a
binary-string ``path`` and either ``{"leaf": true}`` or a zero-based
``{"split": i}``.  For a forest, every record also has a zero-based
``{"root": r}``, and ``--roots`` fixes the expected root count.  This is the
interface a future traced run of the existing verifier can feed without
changing its pruning decisions.
"""

from __future__ import annotations

import argparse
import gzip
import json
import struct
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Iterator, Mapping, Union

MAGIC = b"Z23TREE1"


@dataclass(frozen=True)
class Leaf:
    """A certified terminal box; numeric leaf data lives in another stream."""


@dataclass(frozen=True)
class Split:
    """Midpoint split on a zero-based coordinate."""

    coordinate: int
    lower: "Tree"
    upper: "Tree"


Tree = Union[Leaf, Split]


def preorder(tree: Tree) -> Iterator[int]:
    """Iterative preorder traversal, safe for million-node certificates."""

    stack = [tree]
    while stack:
        node = stack.pop()
        if isinstance(node, Leaf):
            yield 0
        else:
            yield node.coordinate + 1
            stack.append(node.upper)
            stack.append(node.lower)


def validate_tokens(
    tokens: Iterable[int], q: int, roots: int = 1
) -> tuple[int, int, int]:
    """Validate arities and return ``(nodes, splits, leaves)``.

    ``pending`` counts unfilled child slots in the unique preorder parse.  It
    reaches zero exactly at the end of a complete full binary tree.
    """

    if not 1 <= q <= 254:
        raise ValueError("q must lie in [1, 254]")
    if roots <= 0:
        raise ValueError("a certificate forest must have at least one root")
    pending = roots
    nodes = splits = leaves = 0
    for token in tokens:
        if pending == 0:
            raise ValueError("trailing node after a complete tree")
        if not 0 <= token <= q:
            raise ValueError(f"invalid token {token} for q={q}")
        nodes += 1
        if token == 0:
            leaves += 1
            pending -= 1
        else:
            splits += 1
            pending += 1  # consume one slot, create two
    if pending != 0:
        raise ValueError(f"incomplete tree: {pending} child slots remain")
    if leaves != splits + roots:
        raise AssertionError("full-binary-tree invariant failed")
    return nodes, splits, leaves


def encode_forest(trees: Iterable[Tree], q: int) -> bytes:
    roots = list(trees)
    tokens = bytes(token for tree in roots for token in preorder(tree))
    nodes, _, _ = validate_tokens(tokens, q, len(roots))
    return (
        MAGIC
        + bytes([q])
        + struct.pack(">I", len(roots))
        + struct.pack(">Q", nodes)
        + tokens
    )


def encode(tree: Tree, q: int) -> bytes:
    return encode_forest([tree], q)


def validate_blob(blob: bytes) -> tuple[int, int, int, int, int]:
    if len(blob) < len(MAGIC) + 13 or not blob.startswith(MAGIC):
        raise ValueError("bad proof-tree header")
    q = blob[len(MAGIC)]
    roots = struct.unpack(">I", blob[len(MAGIC) + 1 : len(MAGIC) + 5])[0]
    declared = struct.unpack(">Q", blob[len(MAGIC) + 5 : len(MAGIC) + 13])[0]
    tokens = blob[len(MAGIC) + 13 :]
    nodes, splits, leaves = validate_tokens(tokens, q, roots)
    if nodes != declared:
        raise ValueError(f"declared {declared} nodes but decoded {nodes}")
    return q, roots, nodes, splits, leaves


def tree_from_events(records: Iterable[Mapping[str, object]], q: int) -> Tree:
    """Build and validate a tree from path-addressed verifier events."""

    events: Dict[str, Mapping[str, object]] = {}
    for record in records:
        path = record.get("path")
        if not isinstance(path, str) or any(bit not in "01" for bit in path):
            raise ValueError(f"invalid binary path: {path!r}")
        if path in events:
            raise ValueError(f"duplicate path {path!r}")
        events[path] = record

    def build(path: str) -> Tree:
        try:
            record = events[path]
        except KeyError as exc:
            raise ValueError(f"missing event for path {path!r}") from exc
        if record.get("leaf") is True:
            if "split" in record:
                raise ValueError(f"path {path!r} is both leaf and split")
            return Leaf()
        coordinate = record.get("split")
        if not isinstance(coordinate, int) or not 0 <= coordinate < q:
            raise ValueError(f"invalid split at path {path!r}: {coordinate!r}")
        return Split(coordinate, build(path + "0"), build(path + "1"))

    tree = build("")
    reachable = set()
    stack = [""]
    while stack:
        path = stack.pop()
        reachable.add(path)
        if events[path].get("leaf") is not True:
            stack.extend((path + "0", path + "1"))
    extra = set(events) - reachable
    if extra:
        raise ValueError(f"unreachable events, first={min(extra)!r}")
    validate_tokens(preorder(tree), q)
    return tree


def forest_from_events(
    records: Iterable[Mapping[str, object]], q: int, roots: int
) -> list[Tree]:
    """Build an ordered forest from root-indexed path events.

    The one-root case remains backward compatible with old event streams that
    omit ``root``.  Multi-root streams must name every root explicitly; empty,
    duplicate, out-of-range, and missing roots are rejected by this function
    or by :func:`tree_from_events`.
    """

    if roots <= 0:
        raise ValueError("a certificate forest must have at least one root")
    grouped: list[list[Mapping[str, object]]] = [[] for _ in range(roots)]
    for record in records:
        root = record.get("root", 0 if roots == 1 else None)
        if not isinstance(root, int) or not 0 <= root < roots:
            raise ValueError(f"invalid root index: {root!r}")
        grouped[root].append(record)
    trees = []
    for root, events in enumerate(grouped):
        if not events:
            raise ValueError(f"missing events for root {root}")
        trees.append(tree_from_events(events, q))
    validate_tokens(
        (token for tree in trees for token in preorder(tree)), q, roots
    )
    return trees


def read_events(path: Path) -> Iterator[Mapping[str, object]]:
    opener = gzip.open if path.suffix == ".gz" else path.open
    with opener(path, "rt", encoding="utf-8") if path.suffix == ".gz" else opener(
        "r", encoding="utf-8"
    ) as source:
        for line_number, line in enumerate(source, 1):
            if not line.strip():
                continue
            value = json.loads(line)
            if not isinstance(value, dict):
                raise ValueError(f"line {line_number} is not a JSON object")
            yield value


def parse_report(path: Path) -> Dict[str, str]:
    result: Dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        key, separator, value = line.partition("=")
        if separator:
            result[key] = value
    return result


def command_demo(output: Path) -> None:
    tree = Split(0, Split(0, Leaf(), Leaf()), Split(0, Leaf(), Leaf()))
    blob = encode(tree, 1)
    output.write_bytes(blob)
    print(f"wrote={output}")
    print(f"q,nodes,splits,leaves={validate_blob(blob)}")


def command_from_events(events: Path, output: Path, q: int, roots: int) -> None:
    trees = forest_from_events(read_events(events), q, roots)
    blob = encode_forest(trees, q)
    output.write_bytes(blob)
    print(f"wrote={output}")
    print(f"q,nodes,splits,leaves={validate_blob(blob)}")


def command_from_root_dir(
    events_dir: Path, output: Path, roots_output: Path, q: int, roots: int
) -> None:
    """Assemble parallel-safe per-root traces in deterministic root order."""

    trees: list[Tree] = []
    root_boxes: list[object] = []
    for root in range(roots):
        compressed = events_dir / f"root-{root:06d}.events.jsonl.gz"
        plain = events_dir / f"root-{root:06d}.events.jsonl"
        path = compressed if compressed.exists() else plain
        if not path.exists():
            raise ValueError(f"missing event stream for root {root}: {path}")
        records = list(read_events(path))
        root_records = [record for record in records if record.get("path") == ""]
        if len(root_records) != 1 or "root_box" not in root_records[0]:
            raise ValueError(f"root {root} lacks one unambiguous root_box record")
        root_boxes.append(root_records[0]["root_box"])
        trees.append(tree_from_events(records, q))
    blob = encode_forest(trees, q)
    output.write_bytes(blob)
    roots_output.write_text(
        json.dumps({"q": q, "roots": root_boxes}, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    print(f"wrote={output}")
    print(f"roots_wrote={roots_output}")
    print(f"q,nodes,splits,leaves={validate_blob(blob)}")


def command_audit_report(report_path: Path) -> None:
    report = parse_report(report_path)
    nodes = int(report["nodes"])
    splits = int(report["splits"])
    pruned = int(report["pruned"])
    if nodes != splits + pruned:
        raise ValueError("report node count is inconsistent")
    if pruned != splits + int(report["initial_boxes"]):
        raise ValueError("forest leaf count is inconsistent with initial boxes")
    roots = int(report["initial_boxes"])
    byte_count = len(MAGIC) + 13 + nodes
    print(f"nodes={nodes}")
    print(f"roots={roots}")
    print(f"splits={splits}")
    print(f"leaves={pruned}")
    print(f"topology_bytes={byte_count}")


def main() -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    demo = subparsers.add_parser("demo")
    demo.add_argument("output", type=Path)

    events = subparsers.add_parser("from-events")
    events.add_argument("events", type=Path)
    events.add_argument("output", type=Path)
    events.add_argument("--q", type=int, default=6)
    events.add_argument("--roots", type=int, default=1)

    root_dir = subparsers.add_parser("from-root-dir")
    root_dir.add_argument("events_dir", type=Path)
    root_dir.add_argument("output", type=Path)
    root_dir.add_argument("--roots-output", type=Path)
    root_dir.add_argument("--q", type=int, default=6)
    root_dir.add_argument("--roots", type=int, default=324)

    audit = subparsers.add_parser("audit-report")
    audit.add_argument("report", type=Path)

    arguments = parser.parse_args()
    if arguments.command == "demo":
        command_demo(arguments.output)
    elif arguments.command == "from-events":
        command_from_events(
            arguments.events, arguments.output, arguments.q, arguments.roots
        )
    elif arguments.command == "from-root-dir":
        roots_output = arguments.roots_output or arguments.output.with_suffix(
            ".roots.json"
        )
        command_from_root_dir(
            arguments.events_dir, arguments.output, roots_output,
            arguments.q, arguments.roots,
        )
    else:
        command_audit_report(arguments.report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
