/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowClosedHScalable

/-!
# Mixed-frequency cancellation for the current strict `H` certificate

The algebraic frequency `sqrt 2` cancels pairwise against every nonzero
integer multiple of `2 * pi`.  This module proves that cancellation once,
without expanding the six concrete coefficient pairs.
-/

noncomputable section

open Real

namespace Zeta23Ext.CurrentWindowClosedHMixed

open CurrentWindow
open CurrentWindowFiniteCertificate
open CurrentWindowClosedHScalable

private lemma half_sqrt_two_sub_nat_pi_ne_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sqrt 2 / 2 - k * Real.pi ≠ 0 := by
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hp := Real.pi_gt_three
  intro h
  nlinarith

private lemma half_sqrt_two_add_nat_pi_ne_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sqrt 2 / 2 + k * Real.pi ≠ 0 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hp := Real.pi_pos
  have hs := Real.sqrt_nonneg 2
  positivity

private lemma two_sub_periodic_sq_ne_zero (k : ℕ) (hk : k ≠ 0) :
    (2 : ℝ) - (2 * Real.pi * k) ^ 2 ≠ 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hp := Real.pi_gt_three
  have hpk : 3 * (k : ℝ) < Real.pi * k :=
    mul_lt_mul_of_pos_right hp hkpos
  intro h
  have hb : 6 < 2 * Real.pi * k := by nlinarith
  have hprod : 0 < (2 * Real.pi * k - 6) * (2 * Real.pi * k + 6) := by
    positivity
  nlinarith

private lemma sinc_sqrt_two_half :
    Real.sinc (Real.sqrt 2 / 2) =
      2 * Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 := by
  rw [Real.sinc_of_ne_zero (div_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne'
    (by norm_num))]
  ring

private lemma sinc_root_sub_periodic (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((Real.sqrt 2 - 2 * Real.pi * k) / 2) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 - k * Real.pi) := by
  have harg := half_sqrt_two_sub_nat_pi_ne_zero k hk
  rw [show (Real.sqrt 2 - 2 * Real.pi * k) / 2 =
      Real.sqrt 2 / 2 - k * Real.pi by ring,
    Real.sinc_of_ne_zero harg, Real.sin_sub_nat_mul_pi]

private lemma sinc_root_add_periodic (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((Real.sqrt 2 + 2 * Real.pi * k) / 2) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 + k * Real.pi) := by
  have harg := half_sqrt_two_add_nat_pi_ne_zero k hk
  rw [show (Real.sqrt 2 + 2 * Real.pi * k) / 2 =
      Real.sqrt 2 / 2 + k * Real.pi by ring,
    Real.sinc_of_ne_zero harg, Real.sin_add_nat_mul_pi]

private lemma reciprocal_pair (r p : ℝ)
    (hm : r / 2 - p ≠ 0) (hp : r / 2 + p ≠ 0)
    (ht : r ^ 2 - (2 * p) ^ 2 ≠ 0) :
    1 / (r / 2 - p) + 1 / (r / 2 + p) =
      4 * r / (r ^ 2 - (2 * p) ^ 2) := by
  have hm' : r - p * 2 ≠ 0 := by
    intro h
    apply hm
    linarith
  have hp' : r + p * 2 ≠ 0 := by
    intro h
    apply hp
    linarith
  have ht' : r ^ 2 - p ^ 2 * 4 ≠ 0 := by
    convert ht using 1 <;> ring
  field_simp [hm, hp, ht]
  ring_nf
  field_simp [hm', hp', ht']
  ring

private lemma cosCos_root_periodic (k : ℕ) (hk : k ≠ 0) :
    cosCosIntegral (Real.sqrt 2) (2 * Real.pi * k) =
      (-1 : ℝ) ^ k * Real.sinc (Real.sqrt 2 / 2) * 2 /
        (2 - (2 * Real.pi * k) ^ 2) := by
  have hm := sinc_root_sub_periodic k hk
  have hp := sinc_root_add_periodic k hk
  have hdm := half_sqrt_two_sub_nat_pi_ne_zero k hk
  have hdp := half_sqrt_two_add_nat_pi_ne_zero k hk
  have ht := two_sub_periodic_sq_ne_zero k hk
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht' : (Real.sqrt 2) ^ 2 - (2 * (k * Real.pi)) ^ 2 ≠ 0 := by
    rwa [hs, show 2 * (k * Real.pi) = 2 * Real.pi * k by ring]
  have hpair := reciprocal_pair (Real.sqrt 2) (k * Real.pi) hdm hdp ht'
  unfold cosCosIntegral
  rw [hm, hp]
  calc
    ((-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
          (Real.sqrt 2 / 2 - k * Real.pi) +
        (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
          (Real.sqrt 2 / 2 + k * Real.pi)) / 2 =
        ((-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) / 2) *
          (1 / (Real.sqrt 2 / 2 - k * Real.pi) +
            1 / (Real.sqrt 2 / 2 + k * Real.pi)) := by ring
    _ = ((-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) / 2) *
          (4 * Real.sqrt 2 /
            ((Real.sqrt 2) ^ 2 - (2 * (k * Real.pi)) ^ 2)) := by rw [hpair]
    _ = (-1 : ℝ) ^ k * Real.sinc (Real.sqrt 2 / 2) * 2 /
          (2 - (2 * Real.pi * k) ^ 2) := by
      rw [sinc_sqrt_two_half, hs]
      field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2), ht]
      rw [hs]
      ring

private lemma cosCosIntegral_comm (a b : ℝ) :
    cosCosIntegral a b = cosCosIntegral b a := by
  unfold cosCosIntegral
  rw [show (b - a) / 2 = -((a - b) / 2) by ring, Real.sinc_neg]
  ring

/-- Exact cancellation of one algebraic/periodic frequency pair in the two
closed masses. -/
theorem mixed_kernel_cancellation (k : ℕ) (hk : k ≠ 0) :
    cosCosIntegral (Real.sqrt 2) (2 * Real.pi * k) +
        absKernelIntegral (Real.sqrt 2) (2 * Real.pi * k) +
      cosCosIntegral (2 * Real.pi * k) (Real.sqrt 2) +
        absKernelIntegral (2 * Real.pi * k) (Real.sqrt 2) = 0 := by
  have hC := cosCos_root_periodic k hk
  have hCs := cosCosIntegral_comm (2 * Real.pi * k) (Real.sqrt 2)
  have hz : Real.sinc ((k : ℝ) * Real.pi) = 0 := by
    rw [Real.sinc_of_ne_zero
      (mul_ne_zero (Nat.cast_ne_zero.mpr hk) Real.pi_ne_zero),
      Real.sin_nat_mul_pi]
    norm_num
  have hs := Real.sin_nat_mul_pi k
  have hc := Real.cos_nat_mul_pi k
  have hb : (2 * Real.pi * k : ℝ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (Nat.cast_ne_zero.mpr hk)
  have hr : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have ht := two_sub_periodic_sq_ne_zero k hk
  have ht' : (1 : ℝ) - Real.pi ^ 2 * k ^ 2 * 2 ≠ 0 := by
    intro h
    apply ht
    nlinarith
  unfold absKernelIntegral
  rw [hC, hCs, hC]
  rw [show (2 * Real.pi * k) / 2 = (k : ℝ) * Real.pi by ring, hs, hc, hz]
  have hr2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hb, hr, ht]
  ring_nf
  rw [hr2]
  ring_nf
  have hdi : ((1 : ℝ) - Real.pi ^ 2 * k ^ 2 * 2) *
      ((1 : ℝ) - Real.pi ^ 2 * k ^ 2 * 2)⁻¹ = 1 :=
    mul_inv_cancel₀ ht'
  calc
    Real.sinc (Real.sqrt 2 * (1 / 2)) * Real.pi ^ 2 * k ^ 2 *
          ((1 : ℝ) - Real.pi ^ 2 * k ^ 2 * 2)⁻¹ * (-1 : ℝ) ^ k * 4 -
        Real.sinc (Real.sqrt 2 * (1 / 2)) *
          ((1 : ℝ) - Real.pi ^ 2 * k ^ 2 * 2)⁻¹ * (-1 : ℝ) ^ k * 2 +
      Real.sinc (Real.sqrt 2 * (1 / 2)) * (-1 : ℝ) ^ k * 2 =
        2 * Real.sinc (Real.sqrt 2 * (1 / 2)) * (-1 : ℝ) ^ k *
          (1 - ((1 : ℝ) - Real.pi ^ 2 * k ^ 2 * 2) *
            ((1 : ℝ) - Real.pi ^ 2 * k ^ 2 * 2)⁻¹) := by ring
    _ = 0 := by rw [hdi]; ring

private lemma mixed_entry_pair_of_frequency (i : Fin 7) (k : ℕ) (hk : k ≠ 0)
    (hi : frequency i = 2 * Real.pi * k) :
    combinedEntry 0 i + combinedEntry i 0 = 0 := by
  have h := mixed_kernel_cancellation k hk
  unfold combinedEntry
  rw [show frequency 0 = Real.sqrt 2 by norm_num [frequency], hi]
  linear_combination coefficient 0 * coefficient i * h

/-- The six concrete mixed entries in the seven-frequency table cancel in
opposite orientations. -/
theorem mixed_entry_pair (k : Fin 6) :
    combinedEntry 0 k.succ + combinedEntry k.succ 0 = 0 := by
  fin_cases k
  · apply mixed_entry_pair_of_frequency 1 1 (by norm_num)
    norm_num [frequency]
  · apply mixed_entry_pair_of_frequency 2 2 (by norm_num)
    norm_num [frequency]
  · apply mixed_entry_pair_of_frequency 3 3 (by norm_num)
    norm_num [frequency]
  · apply mixed_entry_pair_of_frequency 4 4 (by norm_num)
    norm_num [frequency]
  · apply mixed_entry_pair_of_frequency 5 5 (by norm_num)
    norm_num [frequency]
  · apply mixed_entry_pair_of_frequency 6 6 (by norm_num)
    norm_num [frequency]

theorem mixed_entries_sum :
    (∑ k : Fin 6, (combinedEntry 0 k.succ + combinedEntry k.succ 0)) = 0 := by
  simp_rw [mixed_entry_pair]
  simp

end Zeta23Ext.CurrentWindowClosedHMixed

end
