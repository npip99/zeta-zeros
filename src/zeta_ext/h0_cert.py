"""Rigorous enclosure of the window functional H(v) = 2 - 1/c_1(v).

For v(s) = sum_j c_j cos(omega_j s) on [-1/2, 1/2] (paper eq. (7.3), lambda=1):

    c_1(v) = (int v)^2 / (int v^2 + int int |s-t| v(s) v(t) ds dt).

Closed forms (sinc(z) = sin(z)/z; all removable singularities via sinc):

    I1     = sum_j c_j sinc(omega_j / 2)
    C(a,b) = ( sinc((a-b)/2) + sinc((a+b)/2) ) / 2          [= int cos cos]
    I2     = sum_{i,j} c_i c_j C(omega_i, omega_j)
    A(a,b) = ( sin(a/2)/a + 2 cos(a/2)/a^2 ) sinc(b/2) - (2/a^2) C(a,b)
    J      = sum_{i,j} c_i c_j A(omega_i, omega_j)           [= int int |s-t| v v]

Positivity of v on [-1/2,1/2] (required by the paper's Section 7.1 hypotheses)
is certified separately by interval evaluation on a subdivision.
"""

from __future__ import annotations

from typing import List, Tuple

from flint import arb, fmpq

from .kernel import KernelSpec, sinc_derivatives


def _sinc(z: arb) -> arb:
    return sinc_derivatives(z)[0]


def _omegas(spec: KernelSpec) -> List[arb]:
    result: List[arb] = []
    if spec.has_sqrt2_term:
        result.append(arb(2).sqrt())
    pi = arb.pi()
    for mult in spec.omega_pi_multiples:
        result.append(mult * pi)
    return result


def _cos_cos_integral(a: arb, b: arb) -> arb:
    return (_sinc((a - b) / 2) + _sinc((a + b) / 2)) / 2


def _abs_kernel_integral(a: arb, b: arb) -> arb:
    prefix = (a / 2).sin() / a + 2 * (a / 2).cos() / (a * a)
    return prefix * _sinc(b / 2) - 2 * _cos_cos_integral(a, b) / (a * a)


def window_functional(spec: KernelSpec) -> Tuple[arb, arb]:
    """Return rigorous enclosures (c_1(v), H(v))."""

    omegas = _omegas(spec)
    coeffs = [arb(c) for c in spec.coeffs]

    i1 = arb(0)
    for c, omega in zip(coeffs, omegas):
        i1 += c * _sinc(omega / 2)

    i2 = arb(0)
    j_val = arb(0)
    for ci, oi in zip(coeffs, omegas):
        for cj, oj in zip(coeffs, omegas):
            i2 += ci * cj * _cos_cos_integral(oi, oj)
            j_val += ci * cj * _abs_kernel_integral(oi, oj)

    c_value = i1 * i1 / (i2 + j_val)
    h_value = 2 - 1 / c_value
    return c_value, h_value


def window_min_enclosure(spec: KernelSpec, subdivisions: int = 4096) -> arb:
    """Rigorous lower bound for min of v on [0, 1/2] (v even)."""

    omegas = _omegas(spec)
    coeffs = [arb(c) for c in spec.coeffs]
    best: arb | None = None
    for index in range(subdivisions):
        cell = arb(fmpq(2 * index + 1, 4 * subdivisions),
                   fmpq(1, 4 * subdivisions))
        value = arb(0)
        for c, omega in zip(coeffs, omegas):
            value += c * (omega * cell).cos()
        low = value.lower()
        if best is None or low < best:
            best = low
    assert best is not None
    return arb(best)


def window_monotonicity_enclosures(
    spec: KernelSpec,
    subdivisions: int = 8192,
    origin_cells: int = 4,
) -> Tuple[arb, arb]:
    """Certify that ``v`` is nonincreasing on ``[0, 1/2]``.

    Near the origin, direct interval evaluation of ``v'`` straddles zero
    because ``v'(0) = 0``.  We instead certify ``v'' <= 0`` on the union of
    the first few cells, and use the fundamental theorem of calculus there.
    On the remaining cells we certify ``v' <= 0`` directly.  The returned
    values are, respectively, an upper bound for ``v''`` near zero and the
    largest upper bound for ``v'`` away from zero.
    """

    if not 1 <= origin_cells < subdivisions:
        raise ValueError("origin_cells must lie in [1, subdivisions)")

    omegas = _omegas(spec)
    coeffs = [arb(c) for c in spec.coeffs]

    origin = arb(
        fmpq(origin_cells, 4 * subdivisions),
        fmpq(origin_cells, 4 * subdivisions),
    )
    second = arb(0)
    for coefficient, omega in zip(coeffs, omegas):
        second -= coefficient * omega * omega * (omega * origin).cos()
    second_upper = arb(second.upper())

    derivative_upper = None
    for index in range(origin_cells, subdivisions):
        cell = arb(
            fmpq(2 * index + 1, 4 * subdivisions),
            fmpq(1, 4 * subdivisions),
        )
        derivative = arb(0)
        for coefficient, omega in zip(coeffs, omegas):
            derivative -= coefficient * omega * (omega * cell).sin()
        upper = derivative.upper()
        if derivative_upper is None or upper > derivative_upper:
            derivative_upper = upper

    assert derivative_upper is not None
    return second_upper, arb(derivative_upper)


if __name__ == "__main__":
    from .kernel import MT_SPEC

    c_mt, h_mt = window_functional(MT_SPEC)
    print("c1(MT) =", c_mt.str(25))
    print("H(MT)  =", h_mt.str(25))
    print("min v  =", window_min_enclosure(MT_SPEC, 512).str(10))
