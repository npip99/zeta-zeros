from fractions import Fraction
import unittest

from proof_certificate.shadow_replay import (
    RangeMinimum,
    _box_children,
    dyadic_floor,
    lower_score,
)


class ShadowReplayTests(unittest.TestCase):
    def test_dyadic_floor_is_exact_for_positive_and_negative_values(self):
        self.assertEqual(dyadic_floor(0.5, 4), 8)
        self.assertEqual(dyadic_floor(-0.3, 4), -5)
        value = 0.1
        lower = Fraction(dyadic_floor(value, 20), 1 << 20)
        self.assertLessEqual(lower, Fraction(*value.as_integer_ratio()))

    def test_range_minimum_and_outside_zero(self):
        table = RangeMinimum([9, 4, 7, -2, 8])
        self.assertEqual(table.query_or_zero(0, 0), 9)
        self.assertEqual(table.query_or_zero(1, 4), -2)
        self.assertEqual(table.query_or_zero(0, 5), 0)

    def test_box_children_use_the_lean_midpoint_convention(self):
        box = ((3, 8), (10, 12))
        lower, upper = _box_children(box, 0)
        self.assertEqual(lower, ((3, 5), (10, 12)))
        self.assertEqual(upper, ((6, 8), (10, 12)))

    def test_pressure_only_lower_score(self):
        # Every pair range lies beyond this one-cell table and therefore uses
        # the replay convention's zero kernel lower bound.
        box = tuple((8000, 8000) for _ in range(6))
        score = lower_score(box, RangeMinimum([0]), 8)
        self.assertEqual(score, Fraction(12, 2300))


if __name__ == "__main__":
    unittest.main()
