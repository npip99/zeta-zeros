"""Rigorous Arb enclosures for generalized cosine-window overlap kernels.

The window is v(t) = sum_j c_j cos(omega_j t) on [-1/2, 1/2] (v even, v >= 0).
Its overlap kernel is

    K(x) = integral_{-1/2}^{1/2} v(t) cos(2 pi x t) dt
         = sum_j c_j S(omega_j, 2 pi x),
    S(w, c) = sin((w - c)/2)/(w - c) + sin((w + c)/2)/(w + c)
            = ( sinc((w - c)/2) + sinc((w + c)/2) ) / 2,

with sinc(z) = sin(z)/z (entire).  The Montgomery-Taylor kernel is the single
term c = 1, omega = sqrt(2).

This module provides rigorous lower-bound tables for w(x) = (K(x)/K(0))^2 and
for w''(x) on grid cells, valid for arbitrary term lists, including terms with
omega = 2 pi j whose sinc arguments vanish at integer x (handled by a rigorous
alternating-series evaluation of sinc derivatives near 0).
"""

from __future__ import annotations

import hashlib
import math
import struct
from dataclasses import dataclass
from typing import List, Sequence, Tuple

from flint import arb, ctx, fmpq


def configure_arb(precision: int = 128) -> None:
    if precision < 80:
        raise ValueError("at least 80 bits are required")
    ctx.prec = precision


# ---------------------------------------------------------------------------
# sinc and its first two derivatives, rigorous on any ball.
#
#   sinc(z)   = sum_{n>=0} (-1)^n z^{2n} / (2n+1)!
#   sinc'(z)  = sum_{n>=1} (-1)^n (2n) z^{2n-1} / (2n+1)!
#   sinc''(z) = sum_{n>=1} (-1)^n (2n)(2n-1) z^{2n-2} / (2n+1)!
#
# For |z| <= SERIES_RADIUS the series are evaluated with an explicit rigorous
# tail bound; otherwise closed forms with division are safe.
# ---------------------------------------------------------------------------

SERIES_RADIUS = 0.75
SERIES_TERMS = 24


def _series_tail_bound(radius_pow: arb, n0: int, kind: int) -> arb:
    """Bound |sum_{n>=n0} (-1)^n a_n z^{2n-kind}| by geometric comparison.

    a_n = z^{2n} / (2n+1)! for kind 0, (2n) z^{2n-1}/(2n+1)! for kind 1,
    (2n)(2n-1) z^{2n-2}/(2n+1)! for kind 2.  With |z| <= 3/4 the ratio of
    consecutive terms is at most |z|^2 * (2n+2)(2n+1) / ((2n+3)! / (2n+1)!)
    ... = |z|^2 * poly-ratio < 1/2 for n >= 2, so the tail is at most twice
    the first omitted term.  We use the crude but rigorous bound
    2 * a_{n0} evaluated with |z| replaced by its upper bound.
    """

    fact = arb.fac_ui(2 * n0 + 1)
    if kind == 0:
        first = radius_pow / fact
    elif kind == 1:
        first = (2 * n0) * radius_pow / fact
    else:
        first = (2 * n0) * (2 * n0 - 1) * radius_pow / fact
    return 2 * first


def _sinc_closed(z: arb) -> Tuple[arb, arb, arb]:
    sine = z.sin()
    cosine = z.cos()
    z_squared = z * z
    value = sine / z
    first = (z * cosine - sine) / z_squared
    second = ((2 - z_squared) * sine - 2 * z * cosine) / (z_squared * z)
    return value, first, second


def _intersect(a: arb, b: arb) -> arb:
    try:
        both = a.intersection(b)
    except (AttributeError, ValueError):
        return a
    return both


def sinc_derivatives(z: arb) -> Tuple[arb, arb, arb]:
    """Rigorous enclosures of (sinc, sinc', sinc'') at the ball z.

    Uses the alternating series near zero (tight there, and pole-free), the
    closed form far from zero, and the intersection of both in between.
    """

    upper = z.abs_upper()
    if float(upper) <= SERIES_RADIUS:
        z2 = z * z
        value = arb(1)
        first = arb(0)
        second = arb(0)
        power = arb(1)  # z^{2n-2} running power for n>=1 tracked incrementally
        sign = -1
        z_pow_2n_minus_2 = arb(1)
        for n in range(1, SERIES_TERMS):
            fact = arb.fac_ui(2 * n + 1)
            term_v = z_pow_2n_minus_2 * z2 / fact
            term_d1 = (2 * n) * z_pow_2n_minus_2 * z / fact
            term_d2 = (2 * n) * (2 * n - 1) * z_pow_2n_minus_2 / fact
            if sign > 0:
                value += term_v
                first += term_d1
                second += term_d2
            else:
                value -= term_v
                first -= term_d1
                second -= term_d2
            sign = -sign
            z_pow_2n_minus_2 *= z2
        n0 = SERIES_TERMS
        up = arb(upper)
        up_pow = up ** (2 * n0)
        value += arb(0, float(_series_tail_bound(up_pow, n0, 0).abs_upper()))
        first += arb(0, float(_series_tail_bound(up_pow / up, n0, 1).abs_upper()))
        second += arb(
            0, float(_series_tail_bound(up_pow / (up * up), n0, 2).abs_upper())
        )
        value = _intersect(value, z.sinc())
        if float(z.abs_lower()) >= 0.05:
            cv, cd1, cd2 = _sinc_closed(z)
            value = _intersect(value, cv)
            first = _intersect(first, cd1)
            second = _intersect(second, cd2)
        return value, first, second

    value, first, second = _sinc_closed(z)
    return _intersect(value, z.sinc()), first, second


@dataclass(frozen=True)
class KernelSpec:
    """K(x) = sum_j coeffs[j] * S(omegas[j], 2 pi x); coeffs exact dyadic/rational."""

    coeffs: Tuple[fmpq, ...]
    omega_pi_multiples: Tuple[int, ...]  # omega_j = mult_j * pi for mult>0 entries
    has_sqrt2_term: bool = True  # first term omega = sqrt(2) when True

    def __post_init__(self) -> None:
        expected = len(self.omega_pi_multiples) + (1 if self.has_sqrt2_term else 0)
        if len(self.coeffs) != expected:
            raise ValueError("coefficient count mismatch")


MT_SPEC = KernelSpec(coeffs=(fmpq(1),), omega_pi_multiples=(), has_sqrt2_term=True)


def _omegas(spec: KernelSpec) -> List[arb]:
    result: List[arb] = []
    if spec.has_sqrt2_term:
        result.append(arb(2).sqrt())
    pi = arb.pi()
    for mult in spec.omega_pi_multiples:
        result.append(mult * pi)
    return result


def kernel_k0(spec: KernelSpec) -> arb:
    """K(0) = sum_j c_j * 2 sin(omega_j/2)/omega_j."""

    total = arb(0)
    for coeff, omega in zip(spec.coeffs, _omegas(spec)):
        total += arb(coeff) * 2 * (omega / 2).sin() / omega
    return total


def kernel_derivatives(x: arb, spec: KernelSpec) -> Tuple[arb, arb, arb]:
    """Enclosures of K, K', K'' at the ball x >= 0.

    K(x)  = sum_j c_j (sinc(z-) + sinc(z+)) / 2,  z+- = (omega_j +- 2 pi x)/2
    K'(x) = sum_j c_j pi (-sinc'(z-) + sinc'(z+)) / 2 ... sign: dz-/dx = -pi.
    K''(x)= sum_j c_j pi^2 (sinc''(z-) + sinc''(z+)) / 2.
    """

    pi = arb.pi()
    two_pi_x = 2 * pi * x
    value = arb(0)
    first = arb(0)
    second = arb(0)
    for coeff, omega in zip(spec.coeffs, _omegas(spec)):
        c = arb(coeff)
        z_minus = (omega - two_pi_x) / 2
        z_plus = (omega + two_pi_x) / 2
        v_m, d1_m, d2_m = sinc_derivatives(z_minus)
        v_p, d1_p, d2_p = sinc_derivatives(z_plus)
        value += c * (v_m + v_p) / 2
        first += c * pi * (d1_p - d1_m) / 2
        second += c * pi * pi * (d2_m + d2_p) / 2
    return value, first, second


def squared_kernel_derivatives(
    x: arb, spec: KernelSpec, k0_squared: arb
) -> Tuple[arb, arb, arb]:
    """Enclosures for w(x) = (K/K0)^2 and its first two derivatives."""

    k, k1, k2 = kernel_derivatives(x, spec)
    value = k * k / k0_squared
    first = 2 * k * k1 / k0_squared
    second = 2 * (k1 * k1 + k * k2) / k0_squared
    return value, first, second


def closed_cell(index: int, grid: int) -> arb:
    if index < 0 or grid <= 0:
        raise ValueError("index must be nonnegative and grid must be positive")
    return arb(fmpq(2 * index + 1, 2 * grid), fmpq(1, 2 * grid))


def _nonnegative_lower(value: arb) -> float:
    candidate = float(value.lower())
    if candidate <= 0.0:
        return 0.0
    return math.nextafter(candidate, -math.inf)


def build_w_lower_table(
    grid: int,
    cell_count: int,
    spec: KernelSpec,
    precision: int = 128,
    start: int = 0,
) -> List[float]:
    """Rigorous binary64 lower bounds for min w on cells [start, cell_count)."""

    configure_arb(precision)
    k0 = kernel_k0(spec)
    table: List[float] = []
    for index in range(start, cell_count):
        cell = closed_cell(index, grid)
        k, _, _ = kernel_derivatives(cell, spec)
        ratio_lower = _nonnegative_lower((k / k0).abs_lower())
        table.append(
            math.nextafter(ratio_lower * ratio_lower, -math.inf)
            if ratio_lower > 0.0
            else 0.0
        )
    return table


def build_w_second_lower_table(
    grid: int,
    cell_count: int,
    spec: KernelSpec,
    precision: int = 128,
    start: int = 0,
) -> List[float]:
    """Rigorous lower bounds for w'' on cells [start, cell_count)."""

    configure_arb(precision)
    k0 = kernel_k0(spec)
    k0_squared = k0 * k0
    table: List[float] = []
    for index in range(start, cell_count):
        cell = closed_cell(index, grid)
        _, _, second = squared_kernel_derivatives(cell, spec, k0_squared)
        table.append(math.nextafter(float(second.lower()), -math.inf))
    return table


def table_sha256(values: Sequence[float]) -> str:
    digest = hashlib.sha256()
    for value in values:
        digest.update(struct.pack(">d", value))
    return digest.hexdigest()


class RangeMinimum:
    """O(1) idempotent sparse-table range-minimum queries."""

    def __init__(self, values: Sequence[float]):
        if not values:
            raise ValueError("values must be nonempty")
        self._length = len(values)
        levels: List[List[float]] = [list(values)]
        width = 1
        while 2 * width <= self._length:
            previous = levels[-1]
            half = width
            width *= 2
            levels.append(
                [
                    min(previous[i], previous[i + half])
                    for i in range(self._length - width + 1)
                ]
            )
        self._levels = levels

    @property
    def length(self) -> int:
        return self._length

    def query(self, left: int, right: int) -> float:
        if left < 0 or right < left or right >= self._length:
            raise IndexError((left, right, self._length))
        level = (right - left + 1).bit_length() - 1
        width = 1 << level
        row = self._levels[level]
        return min(row[left], row[right - width + 1])
