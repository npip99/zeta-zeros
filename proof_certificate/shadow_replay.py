#!/usr/bin/env python3
"""Exact-rational feasibility replay for the production certificate.

The production search uses outward-rounded binary64 arithmetic.  Lean's
``CurrentReplay`` layer instead assigns every kernel-table entry one common
dyadic denominator and combines it with the exact rational pressure and pair
weights.  This module checks, before a large Lean artifact is generated, that
the recorded non-tangent leaves and initialization decisions survive that
change of arithmetic.

The raw trace is an input to this audit only.  It is deliberately not copied
into the resulting report or into a proof artifact.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import gzip
import hashlib
import json
import math
from pathlib import Path
import struct
from typing import Iterable, Iterator, Mapping, Sequence

from zeta_ext import design
from zeta_ext.parallel import build_tables_parallel
from zeta_ext.verify_general import cutoff_cell_count


Box = tuple[tuple[int, int], ...]
PAIR_WEIGHTS = {
    key: Fraction(value, design.WEIGHT_DENOMINATOR)
    for key, value in design.WEIGHT_NUMERATORS.items()
    if value
}


@dataclass(frozen=True)
class ScaleResult:
    scale_bits: int
    interval_checked: int
    interval_failed: int
    pressure_checked: int
    pressure_failed: int
    initialization_total: int
    initialization_covered: int
    initialization_score_checked: int
    initialization_failed: int
    tangent_skipped: int
    minimum_interval_margin: Fraction | None
    minimum_pressure_margin: Fraction | None
    minimum_initialization_margin: Fraction | None

    @property
    def passed(self) -> bool:
        return not (
            self.interval_failed
            or self.pressure_failed
            or self.initialization_failed
        )

    def as_json(self) -> dict[str, object]:
        def margin(value: Fraction | None) -> dict[str, object] | None:
            if value is None:
                return None
            return {
                "numerator": value.numerator,
                "denominator": value.denominator,
                "decimal": float(value),
            }

        return {
            "scale_bits": self.scale_bits,
            "passed": self.passed,
            "interval_checked": self.interval_checked,
            "interval_failed": self.interval_failed,
            "pressure_checked": self.pressure_checked,
            "pressure_failed": self.pressure_failed,
            "initialization_total": self.initialization_total,
            "initialization_covered": self.initialization_covered,
            "initialization_score_checked": self.initialization_score_checked,
            "initialization_failed": self.initialization_failed,
            "tangent_skipped": self.tangent_skipped,
            "minimum_interval_margin": margin(self.minimum_interval_margin),
            "minimum_pressure_margin": margin(self.minimum_pressure_margin),
            "minimum_initialization_margin": margin(
                self.minimum_initialization_margin
            ),
        }


class RangeMinimum:
    """Exact integer sparse table with the production query convention."""

    def __init__(self, values: Sequence[int]):
        if not values:
            raise ValueError("a range-minimum table must be nonempty")
        self.length = len(values)
        levels = [list(values)]
        width = 1
        while 2 * width <= len(values):
            previous = levels[-1]
            levels.append(
                [
                    min(previous[i], previous[i + width])
                    for i in range(len(values) - 2 * width + 1)
                ]
            )
            width *= 2
        self.levels = levels

    def query_or_zero(self, left: int, right: int) -> int:
        if left < 0 or right < left:
            raise IndexError((left, right))
        if right >= self.length:
            return 0
        level = (right - left + 1).bit_length() - 1
        width = 1 << level
        row = self.levels[level]
        return min(row[left], row[right - width + 1])


def dyadic_floor(value: float, scale_bits: int) -> int:
    """Largest integer ``n`` with ``n / 2^scale_bits <= value``."""

    if not math.isfinite(value):
        raise ValueError(f"cannot quantize non-finite value {value!r}")
    numerator, denominator = value.as_integer_ratio()
    return (numerator * (1 << scale_bits)) // denominator


def table_sha256(values: Sequence[float]) -> str:
    digest = hashlib.sha256()
    for value in values:
        digest.update(struct.pack(">d", value))
    return digest.hexdigest()


def _box_children(box: Box, coordinate: int) -> tuple[Box, Box]:
    low, high = box[coordinate]
    midpoint = (low + high) // 2
    lower = list(box)
    upper = list(box)
    lower[coordinate] = (low, midpoint)
    upper[coordinate] = (midpoint + 1, high)
    return tuple(lower), tuple(upper)


def _sum_endpoints(box: Box) -> tuple[list[int], list[int]]:
    low_prefix = [0]
    high_prefix = [0]
    for low, high in box:
        low_prefix.append(low_prefix[-1] + low)
        high_prefix.append(high_prefix[-1] + high)
    return low_prefix, high_prefix


def lower_score(
    box: Box,
    ranges: RangeMinimum,
    scale_bits: int,
) -> Fraction:
    """Exact real normalization of Lean's integer ``lowerScore``."""

    low_prefix, high_prefix = _sum_endpoints(box)
    result = Fraction(1, 2300) * Fraction(low_prefix[-1], 4000)
    dyadic_scale = 1 << scale_bits
    for (i, j), weight in PAIR_WEIGHTS.items():
        span = j - i
        left = low_prefix[j] - low_prefix[i]
        right = high_prefix[j] - high_prefix[i] + span - 1
        result += weight * Fraction(
            ranges.query_or_zero(left, right), dyadic_scale
        )
    return result


def _covered(coordinate: int, cell: int) -> bool:
    components = (
        ((3677, 5073), (6869, 45742)),
        ((3784, 4844), (7171, 9845), (10114, 45395)),
        ((3783, 4846), (7168, 9878), (10080, 45398)),
        ((3783, 4846), (7168, 9878), (10080, 45398)),
        ((3784, 4844), (7171, 9845), (10114, 45395)),
        ((3677, 5073), (6869, 45742)),
    )
    return any(low <= cell <= high for low, high in components[coordinate])


def initialization_margins(
    table: Sequence[int], scale_bits: int, cutoff: int
) -> Iterator[Fraction]:
    target = Fraction(509, 100000)
    pressure = Fraction(1, 2300)
    scale = 1 << scale_bits
    for coordinate in range(6):
        exact_weight = PAIR_WEIGHTS[(coordinate, coordinate + 1)]
        for cell in range(cutoff):
            if _covered(coordinate, cell):
                continue
            score = pressure * Fraction(cell, 4000)
            score += exact_weight * Fraction(table[cell], scale)
            yield score - target


def _records(path: Path) -> Iterator[Mapping[str, object]]:
    opener = gzip.open if path.suffix == ".gz" else path.open
    if path.suffix == ".gz":
        source = opener(path, "rt", encoding="utf-8")
    else:
        source = opener("r", encoding="utf-8")
    with source:
        for line in source:
            if line.strip():
                record = json.loads(line)
                if not isinstance(record, dict):
                    raise ValueError(f"non-object trace record in {path}")
                yield record


def trace_leaf_boxes(trace_dir: Path, roots: int = 324) -> Iterator[tuple[str, Box]]:
    """Reconstruct every leaf box while retaining only the DFS frontier."""

    for root in range(roots):
        compressed = trace_dir / f"root-{root:06d}.events.jsonl.gz"
        plain = trace_dir / f"root-{root:06d}.events.jsonl"
        path = compressed if compressed.exists() else plain
        if not path.exists():
            raise FileNotFoundError(path)
        pending: dict[str, Box] = {}
        for record in _records(path):
            address = record.get("path")
            if not isinstance(address, str):
                raise ValueError(f"root {root} has a record without a path")
            if address == "":
                raw_box = record.get("root_box")
                if not isinstance(raw_box, list):
                    raise ValueError(f"root {root} is missing its root box")
                box = tuple((int(part[0]), int(part[1])) for part in raw_box)
            else:
                try:
                    box = pending.pop(address)
                except KeyError as exc:
                    raise ValueError(
                        f"root {root} path {address!r} is out of DFS order"
                    ) from exc
            if record.get("leaf") is True:
                kind = record.get("kind")
                if kind not in {"pressure", "interval", "tangent"}:
                    raise ValueError(f"root {root} has invalid leaf kind {kind!r}")
                yield str(kind), box
                continue
            coordinate = record.get("split")
            if not isinstance(coordinate, int) or not 0 <= coordinate < 6:
                raise ValueError(f"root {root} has invalid split {coordinate!r}")
            lower, upper = _box_children(box, coordinate)
            pending[address + "0"] = lower
            pending[address + "1"] = upper
        if pending:
            raise ValueError(f"root {root} ended with {len(pending)} pending boxes")


@dataclass
class _MutableResult:
    scale_bits: int
    interval_checked: int = 0
    interval_failed: int = 0
    pressure_checked: int = 0
    pressure_failed: int = 0
    initialization_total: int = 0
    initialization_covered: int = 0
    initialization_score_checked: int = 0
    initialization_failed: int = 0
    tangent_skipped: int = 0
    minimum_interval_margin: Fraction | None = None
    minimum_pressure_margin: Fraction | None = None
    minimum_initialization_margin: Fraction | None = None

    def record_leaf(self, kind: str, margin: Fraction) -> None:
        if kind == "interval":
            self.interval_checked += 1
            self.interval_failed += margin < 0
            current = self.minimum_interval_margin
            self.minimum_interval_margin = margin if current is None else min(current, margin)
        elif kind == "pressure":
            self.pressure_checked += 1
            self.pressure_failed += margin < 0
            current = self.minimum_pressure_margin
            self.minimum_pressure_margin = margin if current is None else min(current, margin)
        else:
            self.tangent_skipped += 1

    def freeze(self) -> ScaleResult:
        return ScaleResult(**self.__dict__)


def audit(
    trace_dir: Path,
    scale_bits: Iterable[int],
    workers: int = 6,
) -> tuple[dict[str, object], list[ScaleResult]]:
    spec = design.certificate_spec(4000)
    float_table, second_table = build_tables_parallel(spec, workers)
    cutoff = cutoff_cell_count(spec)
    scales = sorted(set(scale_bits))
    if not scales or scales[0] < 0:
        raise ValueError("scale bits must be nonnegative")
    quantized = {
        bits: [dyadic_floor(value, bits) for value in float_table]
        for bits in scales
    }
    ranges = {bits: RangeMinimum(quantized[bits]) for bits in scales}
    mutable = {bits: _MutableResult(bits) for bits in scales}
    target = Fraction(509, 100000)

    for kind, box in trace_leaf_boxes(trace_dir):
        if kind == "tangent":
            for result in mutable.values():
                result.tangent_skipped += 1
            continue
        for bits in scales:
            margin = lower_score(box, ranges[bits], bits) - target
            mutable[bits].record_leaf(kind, margin)

    for bits in scales:
        result = mutable[bits]
        result.initialization_total = 6 * cutoff
        for margin in initialization_margins(quantized[bits], bits, cutoff):
            result.initialization_score_checked += 1
            result.initialization_failed += margin < 0
            current = result.minimum_initialization_margin
            result.minimum_initialization_margin = (
                margin if current is None else min(current, margin)
            )
        result.initialization_covered = (
            result.initialization_total - result.initialization_score_checked
        )

    metadata: dict[str, object] = {
        "grid": spec.grid,
        "cell_count": len(float_table),
        "cutoff_cells": cutoff,
        "float_kernel_table_sha256": table_sha256(float_table),
        "float_second_table_sha256": table_sha256(second_table),
    }
    return metadata, [mutable[bits].freeze() for bits in scales]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("trace_dir", type=Path)
    parser.add_argument("--scale-bits", default="48,56,64,80")
    parser.add_argument("--workers", type=int, default=6)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    scales = [int(value) for value in arguments.scale_bits.split(",")]
    metadata, results = audit(arguments.trace_dir, scales, arguments.workers)
    report = {
        "format": "zeta23-exact-shadow-v1",
        **metadata,
        "scales": [result.as_json() for result in results],
    }
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if arguments.output is not None:
        arguments.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0 if all(result.passed for result in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
