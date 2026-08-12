#!/usr/bin/env python3
"""Export leaf-tagged topology and exact-rational tangent payloads.

This module is intentionally a *finite artifact producer*.  It does not claim
that an Arb decimal proves a transcendental enclosure.  Instead it turns the
recorded trace into an exact object for the Lean-side semantic checkers:

* ``Z23ANN1`` topology distinguishes regular and tangent leaves and attaches
  a dense 64-bit payload index to each tangent leaf;
* every displayed Arb ball is converted to an exact rational interval;
* every binary64 Hessian coefficient is retained by its exact integer ratio;
* the six-by-six LDL decomposition is recomputed over ``fractions.Fraction``
  and checked by exact reconstruction; and
* the payload records the inclusive kernel-cell range for all 20 nonzero
  pairs, the exact common kernel lower implied by the Hessian coefficient,
  and the exact affine margin.

The semantic proofs for the kernel/value/gradient intervals remain Lean
generator inputs; this exporter neither trusts nor re-evaluates them.
"""

from __future__ import annotations

import argparse
import gzip
import json
import re
import struct
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, Iterator, Mapping, Sequence, TextIO

MAGIC = b"Z23ANN1"
Q = 6

PAIR_NUMERATORS: dict[tuple[int, int], int] = {
    (0, 1): 239252,
    (0, 2): 528172,
    (0, 3): 965879,
    (0, 4): 1000000,
    (0, 5): 1000000,
    (0, 6): 2000000,
    (1, 2): 381335,
    (1, 3): 465776,
    (1, 4): 34121,
    (1, 6): 1000000,
    (2, 3): 379413,
    (2, 4): 12104,
    (2, 5): 34121,
    (2, 6): 1000000,
    (3, 4): 379413,
    (3, 5): 465776,
    (3, 6): 965879,
    (4, 5): 381335,
    (4, 6): 528172,
    (5, 6): 239252,
}
CANONICAL_KEYS = tuple((i, j - i) for i, j in sorted(PAIR_NUMERATORS))

BALL_RE = re.compile(
    r"^\[([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)"
    r" \+/- "
    r"([+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)\]$"
)


def ratio(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def from_ratio(value: object, name: str) -> Fraction:
    if (
        not isinstance(value, list)
        or len(value) != 2
        or not all(isinstance(entry, int) for entry in value)
        or value[1] <= 0
    ):
        raise ValueError(f"{name} is not a positive-denominator integer ratio")
    return Fraction(value[0], value[1])


def parse_ball(text: object, name: str) -> tuple[Fraction, Fraction]:
    """Parse Arb's displayed ``[mid +/- radius]`` as an exact interval."""

    if not isinstance(text, str):
        raise ValueError(f"{name} is not an Arb ball string")
    match = BALL_RE.fullmatch(text)
    if match is None:
        raise ValueError(f"unsupported Arb ball syntax for {name}: {text!r}")
    midpoint = Fraction(Decimal(match.group(1)))
    radius = Fraction(Decimal(match.group(2)))
    if radius < 0:
        raise ValueError(f"negative Arb radius for {name}")
    return midpoint - radius, midpoint + radius


def exact_ldl(
    terms: Sequence[tuple[int, int, Fraction]], q: int = Q
) -> tuple[list[list[Fraction]], list[Fraction], list[list[Fraction]]]:
    """Return exact ``(L,D,M)`` and reject a non-positive pivot."""

    matrix = [[Fraction(0) for _ in range(q)] for _ in range(q)]
    for start, span, coefficient in terms:
        if not 0 <= start < start + span <= q:
            raise ValueError(f"invalid Hessian span ({start}, {span})")
        for row in range(start, start + span):
            for column in range(start, start + span):
                matrix[row][column] += coefficient
    lower = [[Fraction(0) for _ in range(q)] for _ in range(q)]
    diagonal = [Fraction(0) for _ in range(q)]
    for column in range(q):
        lower[column][column] = Fraction(1)
        pivot = matrix[column][column] - sum(
            lower[column][previous] ** 2 * diagonal[previous]
            for previous in range(column)
        )
        if pivot <= 0:
            raise ValueError(f"non-positive exact LDL pivot {column}: {pivot}")
        diagonal[column] = pivot
        for row in range(column + 1, q):
            numerator = matrix[row][column] - sum(
                lower[row][previous]
                * lower[column][previous]
                * diagonal[previous]
                for previous in range(column)
            )
            lower[row][column] = numerator / pivot
    reconstructed = [
        [
            sum(
                lower[row][k] * diagonal[k] * lower[column][k]
                for k in range(q)
            )
            for column in range(q)
        ]
        for row in range(q)
    ]
    if reconstructed != matrix:
        raise AssertionError("exact LDL reconstruction failed")
    return lower, diagonal, matrix


def _box(value: object) -> list[list[int]]:
    if not isinstance(value, list) or len(value) != Q:
        raise ValueError("tangent box must have six coordinates")
    result: list[list[int]] = []
    for coordinate, interval in enumerate(value):
        if (
            not isinstance(interval, list)
            or len(interval) != 2
            or not all(isinstance(endpoint, int) for endpoint in interval)
            or not 0 <= interval[0] <= interval[1]
        ):
            raise ValueError(f"invalid box coordinate {coordinate}")
        result.append(interval)
    return result


def normalize_payload(record: Mapping[str, object], payload_id: int) -> dict[str, object]:
    """Validate one trace tangent record and return canonical exact data."""

    root = record.get("root")
    path = record.get("path")
    if not isinstance(root, int) or root < 0:
        raise ValueError("invalid tangent root")
    if not isinstance(path, str) or any(bit not in "01" for bit in path):
        raise ValueError("invalid tangent path")
    box = _box(record.get("box"))

    raw_terms = record.get("hessian_terms")
    if not isinstance(raw_terms, list):
        raise ValueError("missing hessian_terms")
    terms: list[tuple[int, int, Fraction]] = []
    term_output: list[dict[str, object]] = []
    for index, raw in enumerate(raw_terms):
        if not isinstance(raw, dict):
            raise ValueError(f"hessian term {index} is not an object")
        start, span = raw.get("start"), raw.get("span")
        if not isinstance(start, int) or not isinstance(span, int):
            raise ValueError(f"invalid hessian key {index}")
        coefficient = from_ratio(raw.get("coefficient_ratio"), f"term {index}")
        pair = (start, start + span)
        try:
            pair_weight = Fraction(PAIR_NUMERATORS[pair], 1000000)
        except KeyError as exc:
            raise ValueError(f"unexpected or zero-weight pair {pair}") from exc
        left = sum(box[i][0] for i in range(start, start + span))
        right = sum(box[i][1] for i in range(start, start + span)) + span - 1
        terms.append((start, span, coefficient))
        term_output.append(
            {
                "start": start,
                "span": span,
                "cell_range": [left, right],
                "coefficient": ratio(coefficient),
                "kernel_lower": ratio(coefficient / pair_weight),
            }
        )
    keys = tuple((start, span) for start, span, _ in terms)
    if keys != CANONICAL_KEYS:
        raise ValueError("Hessian terms are not the canonical 20 nonzero pairs")

    midpoints_raw = record.get("midpoints")
    radii_raw = record.get("radii")
    if not isinstance(midpoints_raw, list) or not isinstance(radii_raw, list):
        raise ValueError("missing midpoint/radius vectors")
    if len(midpoints_raw) != Q or len(radii_raw) != Q:
        raise ValueError("midpoint/radius vectors must have length six")
    midpoints = [from_ratio(value, f"midpoint {i}") for i, value in enumerate(midpoints_raw)]
    radii = [from_ratio(value, f"radius {i}") for i, value in enumerate(radii_raw)]
    for i, (midpoint, radius) in enumerate(zip(midpoints, radii)):
        expected_midpoint = Fraction(box[i][0] + box[i][1] + 1, 8000)
        expected_radius = Fraction(box[i][1] - box[i][0] + 1, 8000)
        if midpoint != expected_midpoint or radius != expected_radius:
            raise ValueError(f"midpoint/radius mismatch at coordinate {i}")

    value_interval = parse_ball(record.get("value"), "value")
    gradient_raw = record.get("gradient")
    if not isinstance(gradient_raw, list) or len(gradient_raw) != Q:
        raise ValueError("gradient must contain six Arb balls")
    gradient = [parse_ball(value, f"gradient {i}") for i, value in enumerate(gradient_raw)]
    affine_lower = value_interval[0] - sum(
        max(abs(lower), abs(upper)) * radius
        for (lower, upper), radius in zip(gradient, radii)
    )
    target = Fraction(str(record.get("target")))
    if affine_lower < target:
        raise ValueError(
            f"exact displayed affine bound misses target by {target - affine_lower}"
        )
    trace_lower = parse_ball(record.get("lower"), "lower")

    lower, diagonal, _ = exact_ldl(terms)
    return {
        "id": payload_id,
        "root": root,
        "path": path,
        "box": box,
        "center": [ratio(value) for value in midpoints],
        "radius": [ratio(value) for value in radii],
        "value": [ratio(value_interval[0]), ratio(value_interval[1])],
        "gradient": [[ratio(lo), ratio(hi)] for lo, hi in gradient],
        "hessian_terms": term_output,
        "ldl": {
            "lower": [[ratio(value) for value in row] for row in lower],
            "diagonal": [ratio(value) for value in diagonal],
        },
        "target": ratio(target),
        "affine_lower": ratio(affine_lower),
        "affine_margin": ratio(affine_lower - target),
        "trace_lower": [ratio(trace_lower[0]), ratio(trace_lower[1])],
    }


def read_jsonl(path: Path) -> Iterator[Mapping[str, object]]:
    opener = gzip.open if path.suffix == ".gz" else path.open
    arguments = (path, "rt") if path.suffix == ".gz" else ("r",)
    with opener(*arguments, encoding="utf-8") as source:
        for line_number, line in enumerate(source, 1):
            if not line.strip():
                continue
            value = json.loads(line)
            if not isinstance(value, dict):
                raise ValueError(f"{path}:{line_number} is not an object")
            yield value


@dataclass(frozen=True)
class RootExport:
    topology: bytes
    payloads: list[dict[str, object]]
    nodes: int
    tangent_leaves: int


def export_root(
    events_path: Path, tangent_path: Path, q: int = Q, payload_offset: int = 0
) -> RootExport:
    """Build one deterministic annotated root and its dense payload table."""

    if q != Q:
        raise ValueError("current tangent payloads have dimension six")
    events: Dict[str, Mapping[str, object]] = {}
    for event in read_jsonl(events_path):
        path = event.get("path")
        if not isinstance(path, str) or any(bit not in "01" for bit in path):
            raise ValueError(f"invalid event path {path!r}")
        if path in events:
            raise ValueError(f"duplicate event path {path!r}")
        events[path] = event
    tangent_records: Dict[str, Mapping[str, object]] = {}
    for record in read_jsonl(tangent_path):
        path = record.get("path")
        if not isinstance(path, str) or path in tangent_records:
            raise ValueError(f"invalid or duplicate tangent path {path!r}")
        tangent_records[path] = record

    tokens = bytearray()
    payloads: list[dict[str, object]] = []
    reachable: set[str] = set()
    stack = [""]
    while stack:
        path = stack.pop()
        try:
            event = events[path]
        except KeyError as exc:
            raise ValueError(f"missing event path {path!r}") from exc
        reachable.add(path)
        if event.get("leaf") is True:
            kind = event.get("kind")
            if kind == "tangent":
                try:
                    raw_payload = tangent_records[path]
                except KeyError as exc:
                    raise ValueError(f"missing tangent payload at {path!r}") from exc
                payload_id = payload_offset + len(payloads)
                payload = normalize_payload(raw_payload, payload_id)
                if payload["root"] != event.get("root"):
                    raise ValueError(f"root mismatch at tangent path {path!r}")
                payloads.append(payload)
                tokens.append(1)
                tokens.extend(struct.pack(">Q", payload_id))
            elif kind in {"pressure", "interval"}:
                tokens.append(0)
            else:
                raise ValueError(f"unknown leaf kind {kind!r} at {path!r}")
            continue
        coordinate = event.get("split")
        if not isinstance(coordinate, int) or not 0 <= coordinate < q:
            raise ValueError(f"invalid split at {path!r}")
        tokens.append(coordinate + 2)
        stack.append(path + "1")
        stack.append(path + "0")
    extra = set(events) - reachable
    if extra:
        raise ValueError(f"unreachable event path {min(extra)!r}")
    extra_tangent = set(tangent_records) - {
        payload["path"] for payload in payloads
    }
    if extra_tangent:
        raise ValueError(f"unmatched tangent payload {min(extra_tangent)!r}")
    header = (
        MAGIC
        + bytes([q])
        + struct.pack(">I", 1)
        + struct.pack(">Q", len(events))
        + struct.pack(">Q", len(payloads))
    )
    return RootExport(header + bytes(tokens), payloads, len(events), len(payloads))


def export_forest(trace_dir: Path, roots: int = 324, q: int = Q) -> RootExport:
    """Export all per-root streams in root order with global dense IDs."""

    if roots <= 0:
        raise ValueError("an annotated forest needs at least one root")
    header_size = len(MAGIC) + 1 + 4 + 8 + 8
    bodies = bytearray()
    payloads: list[dict[str, object]] = []
    nodes = 0
    tangent_leaves = 0
    for root in range(roots):
        events = trace_dir / f"root-{root:06d}.events.jsonl.gz"
        tangent = trace_dir / f"root-{root:06d}.tangent.jsonl.gz"
        if not events.exists() or not tangent.exists():
            raise ValueError(f"missing trace stream for root {root}")
        exported = export_root(events, tangent, q, len(payloads))
        bodies.extend(exported.topology[header_size:])
        payloads.extend(exported.payloads)
        nodes += exported.nodes
        tangent_leaves += exported.tangent_leaves
    header = (
        MAGIC
        + bytes([q])
        + struct.pack(">I", roots)
        + struct.pack(">Q", nodes)
        + struct.pack(">Q", tangent_leaves)
    )
    return RootExport(header + bytes(bodies), payloads, nodes, tangent_leaves)


def write_payloads(payloads: Iterable[Mapping[str, object]], destination: TextIO) -> None:
    for payload in payloads:
        destination.write(json.dumps(payload, separators=(",", ":"), sort_keys=True))
        destination.write("\n")


def command_root(
    events: Path, tangent: Path, topology_output: Path, payload_output: Path
) -> None:
    exported = export_root(events, tangent)
    topology_output.write_bytes(exported.topology)
    with payload_output.open("w", encoding="utf-8") as destination:
        write_payloads(exported.payloads, destination)
    print(f"nodes={exported.nodes}")
    print(f"tangent_leaves={exported.tangent_leaves}")
    print(f"topology_bytes={len(exported.topology)}")
    print(f"payload_bytes={payload_output.stat().st_size}")


def command_forest(
    trace_dir: Path, topology_output: Path, payload_output: Path, roots: int
) -> None:
    exported = export_forest(trace_dir, roots)
    topology_output.write_bytes(exported.topology)
    opener = gzip.open if payload_output.suffix == ".gz" else payload_output.open
    arguments = (payload_output, "wt") if payload_output.suffix == ".gz" else ("w",)
    with opener(*arguments, encoding="utf-8") as destination:
        write_payloads(exported.payloads, destination)
    print(f"roots={roots}")
    print(f"nodes={exported.nodes}")
    print(f"tangent_leaves={exported.tangent_leaves}")
    print(f"topology_bytes={len(exported.topology)}")
    print(f"payload_bytes={payload_output.stat().st_size}")


def main() -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    root = subparsers.add_parser("root")
    root.add_argument("events", type=Path)
    root.add_argument("tangent", type=Path)
    root.add_argument("topology_output", type=Path)
    root.add_argument("payload_output", type=Path)
    forest = subparsers.add_parser("forest")
    forest.add_argument("trace_dir", type=Path)
    forest.add_argument("topology_output", type=Path)
    forest.add_argument("payload_output", type=Path)
    forest.add_argument("--roots", type=int, default=324)
    arguments = parser.parse_args()
    if arguments.command == "root":
        command_root(
            arguments.events,
            arguments.tangent,
            arguments.topology_output,
            arguments.payload_output,
        )
    elif arguments.command == "forest":
        command_forest(
            arguments.trace_dir,
            arguments.topology_output,
            arguments.payload_output,
            arguments.roots,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
