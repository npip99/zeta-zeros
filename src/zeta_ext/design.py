"""The certified design: window, weights, and deduction constants.

Vendored from github.com/trmdy/zeta-simple-zeros-673137 (MIT, Tormod Haugland
and contributors); this copy raises the certified target from 1/200 to
509/100000 and re-optimizes the block length, which is the only change.

Every constant here is an exact rational. The design was found by numerical
optimization (see docs/provenance.md) but plays no role in the proof: the
proof is (i) the interval certificates over these exact rationals, and
(ii) the exact deduction of Section 5 of the paper.
"""

from __future__ import annotations

from flint import fmpq

from .kernel import KernelSpec
from .verify_general import CertificateSpec

# Window v(s) = sum_j c_j cos(omega_j s), omega = (sqrt2, 2pi, ..., 12pi).
WINDOW_DENOMINATOR = 10**9
WINDOW_NUMERATORS = (
    1_000_000_000,
    3_322_500,
    -7_609_135,
    1_190_194,
    -731_476,
    -1_680_572,
    1_141_360,
)

KERNEL = KernelSpec(
    coeffs=tuple(fmpq(n, WINDOW_DENOMINATOR) for n in WINDOW_NUMERATORS),
    omega_pi_multiples=(2, 4, 6, 8, 10, 12),
)

# Reflection-symmetric pair weights a_{ij} / 10^6 for the 7-point window
# (0 <= i < j <= 6).  Every span capacity sum_i a_{i,i+r} equals 2 exactly.
WEIGHT_DENOMINATOR = 10**6
WEIGHT_NUMERATORS = {
    (0, 1): 239_252,
    (0, 2): 528_172,
    (0, 3): 965_879,
    (0, 4): 1_000_000,
    (0, 5): 1_000_000,
    (0, 6): 2_000_000,
    (1, 2): 381_335,
    (1, 3): 465_776,
    (1, 4): 34_121,
    (1, 5): 0,
    (1, 6): 1_000_000,
    (2, 3): 379_413,
    (2, 4): 12_104,
    (2, 5): 34_121,
    (2, 6): 1_000_000,
    (3, 4): 379_413,
    (3, 5): 465_776,
    (3, 6): 965_879,
    (4, 5): 381_335,
    (4, 6): 528_172,
    (5, 6): 239_252,
}

PRESSURE = fmpq(1, 2300)
TARGET = fmpq(509, 100000)

# Deduction constants.
BLOCK_LENGTH = 250                     # m
H_CERT = fmpq(672_457, 1_000_000)      # certified lower bound for H(v)
WINDOW_MIN = fmpq(3, 4)                # certified lower bound for v
FINAL_BOUND_RATIONAL = fmpq(673_195, 1_000_000)  # certified <= final bound

# Prior records.
TRMDY_BOUND = "0.673137630699..."
AINTA_BOUND = "0.673008527927..."
ANTHROPIC_H0 = "0.672500703679..."


def certificate_spec(grid: int = 4000) -> CertificateSpec:
    """The main finite inequality F >= 509/100000 as a CertificateSpec."""

    weights = {
        key: fmpq(value, WEIGHT_DENOMINATOR)
        for key, value in WEIGHT_NUMERATORS.items()
        if value
    }
    return CertificateSpec(
        kernel=KERNEL,
        q=6,
        pressure=PRESSURE,
        target=TARGET,
        weights=weights,
        grid=grid,
    )
