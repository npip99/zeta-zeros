"""Closed-form constants occurring in the two certificates."""

from __future__ import annotations

import math


H0 = 1.5 - (1.0 / math.sqrt(2.0)) / math.tan(1.0 / math.sqrt(2.0))
"""Anthropic's Montgomery-Taylor constant (Theorem D)."""

SEVEN_POINT_BETA = 3_826_217 / 1_000_000_000
SEVEN_POINT_BLOCK_SIZE = 267


def three_point_bound(epsilon: float) -> float:
    """Return (H0 - epsilon/4) / (1 - epsilon/2)."""

    if not 0.0 < epsilon <= 1.0:
        raise ValueError("epsilon must lie in (0, 1]")
    return (H0 - epsilon / 4.0) / (1.0 - epsilon / 2.0)


def seven_point_bound() -> float:
    """Return the bound produced by the certified 7-point inequality."""

    m = SEVEN_POINT_BLOCK_SIZE
    numerator = H0 - (1.0 / 500.0) * (m - 1) / m
    denominator = 1.0 - SEVEN_POINT_BETA * (m - 6) / m
    return numerator / denominator
