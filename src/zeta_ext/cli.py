"""Command-line entry points for the certificates.

  zeta-ext-verify gate   -- reproduce the ainta 7-point certificate
  zeta-ext-verify fast   -- window bounds, monotonicity, H(v), and deduction
  zeta-ext-verify main   -- the main inequality F >= 509/100000 (parallel)
  zeta-ext-verify all    -- fast + main
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

from flint import arb, ctx, fmpq

from . import design
from .h0_cert import (
    window_functional,
    window_min_enclosure,
    window_monotonicity_enclosures,
)
from .kernel import MT_SPEC
from .parallel import verify_parallel
from .verify_general import CertificateSpec, uniform_weights, verify_general


def run_gate(args: argparse.Namespace) -> int:
    spec = CertificateSpec(
        kernel=MT_SPEC,
        q=6,
        pressure=fmpq(1, 3000),
        target=fmpq(19, 5000),
        weights=uniform_weights(6),
        grid=4000,
    )
    if args.workers > 1:
        report = verify_parallel(
            spec, workers=args.workers,
            trace_dir=Path(args.trace_dir) if args.trace_dir else None,
        )
    else:
        report = verify_general(
            spec, progress_every=200_000,
            trace_dir=Path(args.trace_dir) if args.trace_dir else None,
        )
    print("\n".join(report.lines()))
    print("expected_nodes=707797 (matches ainta's committed run up to table "
          "tightness; their run records 707901)")
    return 0 if report.verified else 1


def run_fast(_: argparse.Namespace) -> int:
    ctx.prec = 192
    ok = True

    low = window_min_enclosure(design.KERNEL, subdivisions=8192)
    good = bool(low >= arb(design.WINDOW_MIN))
    ok &= good
    print(f"min v >= {low.str(15)}  [>= 3/4: {good}]")

    # max v <= 1 via the same subdivision on the reflected bound.
    from .h0_cert import _omegas  # noqa: PLC2701

    omegas = _omegas(design.KERNEL)
    coeffs = [arb(c) for c in design.KERNEL.coeffs]
    hi = None
    n = 8192
    for i in range(n):
        cell = arb(fmpq(2 * i + 1, 4 * n), fmpq(1, 4 * n))
        value = arb(0)
        for c, om in zip(coeffs, omegas):
            value += c * (om * cell).cos()
        upper = value.upper()
        hi = upper if hi is None or upper > hi else hi
    good = bool(arb(hi) <= arb(1))
    ok &= good
    print(f"max v <= {arb(hi).str(15)}  [<= 1: {good}]")

    second_near_zero, derivative_away = window_monotonicity_enclosures(
        design.KERNEL, subdivisions=8192
    )
    good = bool(second_near_zero <= arb(0) and derivative_away <= arb(0))
    ok &= good
    print(
        "monotone on [0,1/2]: "
        f"v'' near 0 <= {second_near_zero.str(12)}, "
        f"v' away <= {derivative_away.str(12)}  [certified: {good}]"
    )

    c_val, h_val = window_functional(design.KERNEL)
    good = bool(h_val >= arb(design.H_CERT))
    ok &= good
    print(f"c1(v) = {c_val.str(20)}")
    print(f"H(v)  = {h_val.str(20)}  [>= {design.H_CERT}: {good}]")

    m = design.BLOCK_LENGTH
    eps = arb(design.TARGET)
    p = arb(design.PRESSURE)
    q = 6
    h_low = arb(design.H_CERT)
    a_val = eps * (m - q)
    r_val = 2 * a_val.sqrt() - 1
    eta = r_val / a_val
    b_press = q * p
    bound = (m * h_low - eta * b_press * (m - 1)) / (m - r_val)
    good = bool(bound >= arb(design.FINAL_BOUND_RATIONAL))
    ok &= good
    print(f"A = {a_val.str(10)}  R = {r_val.str(18)}")
    print(f"final bound = {bound.str(22)}  "
          f"[>= {design.FINAL_BOUND_RATIONAL}: {good}]")
    print(f"fast_parts_verified={ok}")
    return 0 if ok else 1


def run_main(args: argparse.Namespace) -> int:
    spec = design.certificate_spec(grid=args.grid)
    started = time.time()
    if args.workers > 1:
        report = verify_parallel(
            spec, workers=args.workers,
            trace_dir=Path(args.trace_dir) if args.trace_dir else None,
        )
    else:
        report = verify_general(
            spec, progress_every=200_000,
            trace_dir=Path(args.trace_dir) if args.trace_dir else None,
        )
    print("\n".join(report.lines()))
    print(f"wall_seconds={time.time() - started:.1f}")
    return 0 if report.verified else 1


def main() -> int:
    parser = argparse.ArgumentParser(prog="zeta-ext-verify")
    parser.add_argument("command", choices=["gate", "fast", "main", "all"])
    parser.add_argument("--grid", type=int, default=4000)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument(
        "--trace-dir",
        help="optional directory for per-root topology and tangent evidence",
    )
    args = parser.parse_args()
    if args.command == "gate":
        return run_gate(args)
    if args.command == "fast":
        return run_fast(args)
    if args.command == "main":
        return run_main(args)
    status = run_fast(args)
    return status or run_main(args)


if __name__ == "__main__":
    sys.exit(main())
