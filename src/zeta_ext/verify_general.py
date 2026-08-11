"""Computer-assisted certificate for generalized q-gap pressure inequalities.

Proves, by exhaustive interval subdivision, statements of the form

    F(g_1..g_q) = p * sum_i g_i
                + sum_{0<=i<j<=q} a_{ij} w(y_j - y_i)  >=  target

for all nonnegative gaps, where y_j = g_1 + ... + g_j, w = (K/K(0))^2 for a
KernelSpec kernel, p and target are exact rationals, and the pair weights
a_{ij} are exact nonnegative rationals satisfying the window capacity
constraint sum_i a_{i,i+r} <= 2 for every span r (checked here).

Adapted from zeta-simple-zeros verify_seven.py (MIT); generalized to arbitrary
kernel, weights, pressure, target, and grid.
"""

from __future__ import annotations

import itertools
import math
import time
from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from flint import arb, fmpq

from .kernel import (
    KernelSpec,
    RangeMinimum,
    build_w_lower_table,
    build_w_second_lower_table,
    closed_cell,
    kernel_k0,
    squared_kernel_derivatives,
    table_sha256,
)


@dataclass(frozen=True)
class CertificateSpec:
    kernel: KernelSpec
    q: int                      # number of gaps (window has q+1 points)
    pressure: fmpq              # p
    target: fmpq                # certified lower bound for F
    weights: Dict[Tuple[int, int], fmpq]  # (i, j) -> a_{ij}, 0 <= i < j <= q
    grid: int = 4000
    precision: int = 128
    extra_cells: int = 8
    # When False, the convex-tangent pruner is disabled and the certificate
    # rests on pure interval subdivision only (slower; used as a hardening
    # re-verification because table errors can then only cause false
    # failure, never false certification).
    use_tangent: bool = True

    def capacity_ok(self) -> bool:
        for r in range(1, self.q + 1):
            total = fmpq(0)
            for i in range(0, self.q - r + 1):
                total += self.weights.get((i, i + r), fmpq(0))
            if total > 2:
                return False
        return True


def uniform_weights(q: int) -> Dict[Tuple[int, int], fmpq]:
    """The canonical homogeneous weights a_{ij} = 2/(q+1-(j-i))."""

    weights: Dict[Tuple[int, int], fmpq] = {}
    for i in range(q + 1):
        for j in range(i + 1, q + 1):
            weights[(i, j)] = fmpq(2, q + 1 - (j - i))
    return weights


@dataclass
class GeneralReport:
    verified: bool
    target: str
    grid: int
    nodes: int
    pruned: int
    splits: int
    maximum_depth: int
    initial_boxes: int
    elapsed_seconds: float
    details: Dict[str, object] = field(default_factory=dict)

    def lines(self) -> List[str]:
        out = [f"verified={self.verified}", f"target={self.target}",
               f"grid={self.grid}", f"nodes={self.nodes}",
               f"pruned={self.pruned}", f"splits={self.splits}",
               f"maximum_depth={self.maximum_depth}",
               f"initial_boxes={self.initial_boxes}",
               f"elapsed_seconds={self.elapsed_seconds:.3f}"]
        out.extend(f"{k}={v}" for k, v in sorted(self.details.items()))
        return out


CellRange = Tuple[int, int]


def _down(value: float) -> float:
    return math.nextafter(value, -math.inf)


def _up(value: float) -> float:
    return math.nextafter(value, math.inf)


def _fmpq_lower(value: fmpq) -> float:
    return _down(int(value.p) / int(value.q))


def _fmpq_upper(value: fmpq) -> float:
    return _up(int(value.p) / int(value.q))


def _components(indices: Iterable[int]) -> List[CellRange]:
    result: List[List[int]] = []
    for index in indices:
        if not result or index > result[-1][1] + 1:
            result.append([index, index])
        else:
            result[-1][1] = index
    return [(left, right) for left, right in result]


def cutoff_cell_count(spec: CertificateSpec) -> int:
    """Cells after which pressure alone certifies the target."""

    cutoff_units = spec.target / spec.pressure
    return int(
        math.ceil(_up(int(cutoff_units.p) / int(cutoff_units.q)) * spec.grid)
    ) + 1


def build_tables(spec: CertificateSpec) -> Tuple[List[float], List[float]]:
    cell_count = cutoff_cell_count(spec) + spec.extra_cells
    table = build_w_lower_table(
        spec.grid, cell_count, spec.kernel, spec.precision
    )
    second_table = build_w_second_lower_table(
        spec.grid, cell_count, spec.kernel, spec.precision
    )
    return table, second_table


def verify_general(
    spec: CertificateSpec,
    progress_every: int = 0,
    shard: int = 0,
    shard_count: int = 1,
    tables: Optional[Tuple[List[float], List[float]]] = None,
) -> GeneralReport:
    if not spec.capacity_ok():
        raise ValueError("weights violate the span capacity constraint")
    if not (0 <= shard < shard_count):
        raise ValueError("invalid shard")

    started = time.perf_counter()
    q = spec.q
    grid = spec.grid

    from .kernel import configure_arb

    configure_arb(spec.precision)
    cutoff_cells = cutoff_cell_count(spec)
    if tables is None:
        tables = build_tables(spec)
    table, second_table = tables
    if len(table) < cutoff_cells:
        raise ValueError("supplied table too short for the pressure cutoff")
    ranges = RangeMinimum(table)
    second_ranges = RangeMinimum(second_table)
    k0 = kernel_k0(spec.kernel)
    k0_squared = k0 * k0

    target_upper = _fmpq_upper(spec.target)
    pressure_lower = _fmpq_lower(spec.pressure)

    # Weight lookup as outward-rounded floats (lower bounds; weights >= 0) and
    # upper bounds for signed multiplication in the Hessian bound.
    weight_lower: Dict[Tuple[int, int], float] = {}
    weight_upper: Dict[Tuple[int, int], float] = {}
    weight_arb: Dict[Tuple[int, int], arb] = {}
    for key, value in spec.weights.items():
        weight_lower[key] = _fmpq_lower(value)
        weight_upper[key] = _fmpq_upper(value)
        weight_arb[key] = arb(value)

    def kernel_min(left: int, right: int) -> float:
        if right >= ranges.length:
            return 0.0
        return ranges.query(left, right)

    def second_min(left: int, right: int) -> float:
        if right >= second_ranges.length:
            return float("-inf")
        return second_ranges.query(left, right)

    # One-body pruning per coordinate: U_i(g) = p g + a_{i,i+1} w(g).
    coordinate_components: List[List[CellRange]] = []
    for coordinate in range(q):
        weight = weight_lower.get((coordinate, coordinate + 1), 0.0)
        surviving = []
        for index in range(cutoff_cells):
            one_body = _down(pressure_lower * index / grid)
            one_body = _down(one_body + _down(weight * table[index]))
            if one_body < target_upper:
                surviving.append(index)
        coordinate_components.append(_components(surviving))

    stack: List[Tuple[Tuple[CellRange, ...], int]] = [
        (tuple(parts), 0)
        for index, parts in enumerate(itertools.product(*coordinate_components))
        if index % shard_count == shard
    ]
    initial_boxes = len(stack)
    nodes = pruned = splits = maximum_depth = 0
    pressure_pruned = interval_pruned = tangent_pruned = 0

    pair_list = sorted(spec.weights)

    def box_lower(box: Sequence[CellRange]) -> float:
        low_prefix = [0]
        high_prefix = [0]
        for low, high in box:
            low_prefix.append(low_prefix[-1] + low)
            high_prefix.append(high_prefix[-1] + high)
        result = _down(pressure_lower * low_prefix[-1] / grid)
        for i, j in pair_list:
            span = j - i
            left = low_prefix[j] - low_prefix[i]
            right = high_prefix[j] - high_prefix[i] + span - 1
            result = _down(
                result + _down(weight_lower[(i, j)] * kernel_min(left, right))
            )
        return result

    def signed_lower_product(weight_key: Tuple[int, int], lower: float) -> float:
        if lower == float("-inf"):
            return lower
        factor = (
            weight_lower[weight_key] if lower >= 0.0 else weight_upper[weight_key]
        )
        return _down(factor * lower)

    def float_ldl_is_positive(matrix: List[List[float]]) -> bool:
        lower = [[0.0] * q for _ in range(q)]
        diagonal = [0.0] * q
        for column in range(q):
            pivot = matrix[column][column]
            for previous in range(column):
                pivot -= (
                    lower[column][previous] ** 2 * diagonal[previous]
                )
            if pivot <= 1e-12:
                return False
            diagonal[column] = pivot
            lower[column][column] = 1.0
            for row in range(column + 1, q):
                value = matrix[row][column]
                for previous in range(column):
                    value -= (
                        lower[row][previous]
                        * lower[column][previous]
                        * diagonal[previous]
                    )
                lower[row][column] = value / pivot
        return True

    def exact_float(value: float) -> arb:
        numerator, denominator = value.as_integer_ratio()
        return arb(fmpq(numerator, denominator))

    def arb_ldl_is_positive(terms: Sequence[Tuple[int, int, float]]) -> bool:
        matrix = [[arb(0) for _ in range(q)] for _ in range(q)]
        for start, span, coefficient in terms:
            exact = exact_float(coefficient)
            for row in range(start, start + span):
                for column in range(start, start + span):
                    matrix[row][column] += exact
        lower = [[arb(0) for _ in range(q)] for _ in range(q)]
        diagonal = [arb(0) for _ in range(q)]
        for column in range(q):
            lower[column][column] = arb(1)
            pivot = matrix[column][column]
            for previous in range(column):
                pivot -= (
                    lower[column][previous]
                    * lower[column][previous]
                    * diagonal[previous]
                )
            if not (pivot > 0):
                return False
            diagonal[column] = pivot
            for row in range(column + 1, q):
                value = matrix[row][column]
                for previous in range(column):
                    value -= (
                        lower[row][previous]
                        * lower[column][previous]
                        * diagonal[previous]
                    )
                lower[row][column] = value / pivot
        return True

    target_arb = arb(spec.target)
    pressure_arb = arb(spec.pressure)

    def convex_tangent_lower(box: Sequence[CellRange]) -> Optional[arb]:
        low_prefix = [0]
        high_prefix = [0]
        for low, high in box:
            low_prefix.append(low_prefix[-1] + low)
            high_prefix.append(high_prefix[-1] + high)

        terms: List[Tuple[int, int, float]] = []
        heuristic = [[0.0] * q for _ in range(q)]
        for i, j in pair_list:
            span = j - i
            left = low_prefix[j] - low_prefix[i]
            right = high_prefix[j] - high_prefix[i] + span - 1
            second_lower = second_min(left, right)
            scalar = signed_lower_product((i, j), second_lower)
            if scalar == float("-inf"):
                return None
            terms.append((i, span, scalar))
            for row in range(i, i + span):
                for column in range(i, i + span):
                    heuristic[row][column] += scalar

        if not float_ldl_is_positive(heuristic):
            return None
        if not arb_ldl_is_positive(terms):
            return None

        midpoints = [fmpq(low + high + 1, 2 * grid) for low, high in box]
        radii = [fmpq(high - low + 1, 2 * grid) for low, high in box]
        value = sum((arb(point) for point in midpoints), arb(0)) * pressure_arb
        gradient = [arb(spec.pressure) for _ in range(q)]

        for i, j in pair_list:
            coefficient = weight_arb[(i, j)]
            point = sum(midpoints[i:j], fmpq(0))
            potential, derivative, _ = squared_kernel_derivatives(
                arb(point), spec.kernel, k0_squared
            )
            value += coefficient * potential
            for coordinate in range(i, j):
                gradient[coordinate] += coefficient * derivative

        lower = value
        for derivative, radius in zip(gradient, radii):
            lower -= derivative.abs_upper() * arb(radius)
        return lower

    while stack:
        box, depth = stack.pop()
        nodes += 1
        maximum_depth = max(maximum_depth, depth)

        if sum(part[0] for part in box) >= cutoff_cells:
            pruned += 1
            pressure_pruned += 1
            continue

        lower = box_lower(box)
        if lower >= target_upper:
            pruned += 1
            interval_pruned += 1
            continue

        tangent_lower = convex_tangent_lower(box) if spec.use_tangent else None
        if tangent_lower is not None and tangent_lower >= target_arb:
            pruned += 1
            tangent_pruned += 1
            continue

        widths = [right - left for left, right in box]
        if max(widths) == 0:
            raise RuntimeError(
                f"certificate failed at a terminal cell: box={box}, lower={lower}"
            )

        splits += 1
        coordinate = max(range(q), key=widths.__getitem__)
        left, right = box[coordinate]
        midpoint = (left + right) // 2
        lower_half = list(box)
        upper_half = list(box)
        lower_half[coordinate] = (left, midpoint)
        upper_half[coordinate] = (midpoint + 1, right)
        stack.append((tuple(lower_half), depth + 1))
        stack.append((tuple(upper_half), depth + 1))

        if progress_every and nodes % progress_every == 0:
            print(
                f"general: nodes={nodes} pending={len(stack)} "
                f"depth={maximum_depth} pruned={pruned}",
                flush=True,
            )

    elapsed = time.perf_counter() - started
    return GeneralReport(
        verified=True,
        target=f"F >= {spec.target}",
        grid=grid,
        nodes=nodes,
        pruned=pruned,
        splits=splits,
        maximum_depth=maximum_depth,
        initial_boxes=initial_boxes,
        elapsed_seconds=elapsed,
        details={
            "pressure_pruned": pressure_pruned,
            "interval_pruned": interval_pruned,
            "tangent_pruned": tangent_pruned,
            "cutoff_cells": cutoff_cells,
            "w_table_sha256": table_sha256(table),
            "w_second_table_sha256": table_sha256(second_table),
        },
    )
