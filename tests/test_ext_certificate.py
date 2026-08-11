import unittest

from flint import arb, ctx

from zeta_ext import design
from zeta_ext.h0_cert import (
    window_functional,
    window_min_enclosure,
    window_monotonicity_enclosures,
)


class ExtendedCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 192

    def test_weight_capacities_are_exactly_two(self):
        for span in range(1, 7):
            capacity = sum(
                design.certificate_spec().weights.get((i, i + span), 0)
                for i in range(7 - span)
            )
            self.assertEqual(capacity, 2)

    def test_window_bounds_and_monotonicity(self):
        self.assertGreaterEqual(
            window_min_enclosure(design.KERNEL, subdivisions=8192),
            arb(design.WINDOW_MIN),
        )
        second_near_zero, derivative_away = window_monotonicity_enclosures(
            design.KERNEL, subdivisions=8192
        )
        self.assertLessEqual(second_near_zero, arb(0))
        self.assertLessEqual(derivative_away, arb(0))

    def test_window_functional_and_final_bound(self):
        _, h_value = window_functional(design.KERNEL)
        self.assertGreaterEqual(h_value, arb(design.H_CERT))

        m = design.BLOCK_LENGTH
        a_value = arb(design.TARGET) * (m - 6)
        r_value = 2 * a_value.sqrt() - 1
        eta = r_value / a_value
        bound = (
            m * arb(design.H_CERT)
            - eta * 6 * arb(design.PRESSURE) * (m - 1)
        ) / (m - r_value)
        self.assertGreaterEqual(bound, arb(design.FINAL_BOUND_RATIONAL))


if __name__ == "__main__":
    unittest.main()
