/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowFiniteCertificate

/-!
# Kernel-checked numeric reduction of the current `H` certificate

The six periodic frequencies make the apparent seven-by-seven closed form
much smaller than a generic transcendental interval problem.  This file
develops the extra-precision Taylor bounds needed by that reduction and
checks the final rational inequality.  The remaining theorem in this lane is
the exact algebraic identification of the two finite sums with `compactMass`.
-/

noncomputable section

open Real Set

namespace Zeta23Ext.CurrentWindowClosedHCertificate

open CurrentWindow
open CurrentWindowFiniteCertificate

private lemma frequency_eq_explicit : frequency = fun j : Fin 7 =>
    match j.1 with
    | 0 => Real.sqrt 2
    | 1 => 2 * Real.pi
    | 2 => 2 * Real.pi * 2
    | 3 => 2 * Real.pi * 3
    | 4 => 2 * Real.pi * 4
    | 5 => 2 * Real.pi * 5
    | _ => 2 * Real.pi * 6 := by
  funext j
  fin_cases j <;> norm_num [frequency]

lemma sinc_nat_mul_pi_eq_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((k : ℝ) * Real.pi) = 0 := by
  rw [Real.sinc_of_ne_zero]
  · rw [Real.sin_nat_mul_pi]
    norm_num
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr hk) Real.pi_ne_zero

private lemma sinc_sqrt_two_sub_periodic (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((Real.sqrt 2 - 2 * Real.pi * k) / 2) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 - k * Real.pi) := by
  have hr : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have harg : Real.sqrt 2 / 2 - k * Real.pi ≠ 0 := by
    have := Real.pi_gt_three
    nlinarith
  rw [show (Real.sqrt 2 - 2 * Real.pi * k) / 2 =
      Real.sqrt 2 / 2 - k * Real.pi by ring, Real.sinc_of_ne_zero harg,
    Real.sin_sub_nat_mul_pi]

private lemma sinc_sqrt_two_add_periodic (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((Real.sqrt 2 + 2 * Real.pi * k) / 2) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 + k * Real.pi) := by
  have harg : Real.sqrt 2 / 2 + k * Real.pi ≠ 0 := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have := Real.pi_pos
    have := Real.sqrt_nonneg 2
    positivity
  rw [show (Real.sqrt 2 + 2 * Real.pi * k) / 2 =
      Real.sqrt 2 / 2 + k * Real.pi by ring, Real.sinc_of_ne_zero harg,
    Real.sin_add_nat_mul_pi]

private lemma sinc_periodic_sub_sqrt_two (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((2 * Real.pi * k - Real.sqrt 2) / 2) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 - k * Real.pi) := by
  rw [show (2 * Real.pi * k - Real.sqrt 2) / 2 =
      -((Real.sqrt 2 - 2 * Real.pi * k) / 2) by ring, Real.sinc_neg,
    sinc_sqrt_two_sub_periodic k hk]

private lemma sinc_periodic_add_sqrt_two (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((2 * Real.pi * k + Real.sqrt 2) / 2) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 + k * Real.pi) := by
  rw [add_comm, sinc_sqrt_two_add_periodic k hk]

private lemma sinc_sqrt_two_half :
    Real.sinc (Real.sqrt 2 / 2) =
      2 * Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 := by
  rw [Real.sinc_of_ne_zero (div_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne'
    (by norm_num))]
  ring

private lemma sinc_sqrt_two :
    Real.sinc (Real.sqrt 2) =
      2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) /
        Real.sqrt 2 := by
  rw [Real.sinc_of_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne']
  rw [show Real.sqrt 2 = Real.sqrt 2 / 2 + Real.sqrt 2 / 2 by ring,
    Real.sin_add]
  ring

/-! ## Higher-precision endpoint bounds -/

def sinTaylor13 (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 +
    x ^ 9 / 362880 - x ^ 11 / 39916800 + x ^ 13 / 6227020800

lemma sinTaylorWithin_thirteen {upper x : ℝ} (hupper : 0 < upper) :
    TranscendentalBounds.sinTaylorWithin 13 upper x = sinTaylor13 x := by
  have hderiv : ∀ k : ℕ,
      iteratedDerivWithin k Real.sin (Set.Icc (0 : ℝ) upper) 0 =
        iteratedDeriv k Real.sin 0 := by
    intro k
    exact Real.iteratedDerivWithin_sin_Icc k hupper ⟨le_rfl, hupper.le⟩
  rw [TranscendentalBounds.sinTaylorWithin, taylor_within_apply]
  simp_rw [hderiv]
  norm_num [sinTaylor13, Real.iteratedDeriv_even_sin,
    Real.iteratedDeriv_odd_sin, Finset.sum_range_succ]
  ring

lemma abs_sin_sub_sinTaylor13_le {upper x : ℝ} (hupper : 0 < upper)
    (hx : x ∈ Set.Icc (0 : ℝ) upper) :
    |Real.sin x - sinTaylor13 x| ≤ x ^ 14 / 6227020800 := by
  rw [← sinTaylorWithin_thirteen hupper]
  have h := TranscendentalBounds.abs_sin_sub_sinTaylorWithin_le 13 hupper hx
  norm_num at h ⊢
  exact h

def cosTaylor12 (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 +
    x ^ 8 / 40320 - x ^ 10 / 3628800 + x ^ 12 / 479001600

lemma cosTaylorWithin_twelve {upper x : ℝ} (hupper : 0 < upper) :
    TranscendentalBounds.cosTaylorWithin 12 upper x = cosTaylor12 x := by
  have hderiv : ∀ k : ℕ,
      iteratedDerivWithin k Real.cos (Set.Icc (0 : ℝ) upper) 0 =
        iteratedDeriv k Real.cos 0 := by
    intro k
    exact Real.iteratedDerivWithin_cos_Icc k hupper ⟨le_rfl, hupper.le⟩
  rw [TranscendentalBounds.cosTaylorWithin, taylor_within_apply]
  simp_rw [hderiv]
  norm_num [cosTaylor12, Real.iteratedDeriv_even_cos,
    Real.iteratedDeriv_odd_cos, Finset.sum_range_succ]
  ring

lemma abs_cos_sub_cosTaylor12_le {upper x : ℝ} (hupper : 0 < upper)
    (hx : x ∈ Set.Icc (0 : ℝ) upper) :
    |Real.cos x - cosTaylor12 x| ≤ x ^ 13 / 479001600 := by
  rw [← cosTaylorWithin_twelve hupper]
  have h := TranscendentalBounds.abs_cos_sub_cosTaylorWithin_le 12 hupper hx
  norm_num at h ⊢
  exact h

lemma sqrt_two_tight :
    (14142135623 : ℝ) / 10000000000 ≤ Real.sqrt 2 ∧
      Real.sqrt 2 ≤ (3535533906 : ℝ) / 2500000000 := by
  apply TranscendentalBounds.sqrt_mem_interval (x := (2 : ℝ)) <;> norm_num

private lemma sqrt_two_powers :
    let r := Real.sqrt 2
    r ^ 2 = 2 ∧ r ^ 3 = 2 * r ∧ r ^ 4 = 4 ∧ r ^ 5 = 4 * r ∧
    r ^ 6 = 8 ∧ r ^ 7 = 8 * r ∧ r ^ 8 = 16 ∧ r ^ 9 = 16 * r ∧
    r ^ 10 = 32 ∧ r ^ 11 = 32 * r ∧ r ^ 12 = 64 ∧
    r ^ 13 = 64 * r ∧ r ^ 14 = 128 := by
  dsimp
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · exact h2
  constructor
  · calc (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
         _ = 2 * Real.sqrt 2 := by rw [h2]
  constructor
  · calc (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
         _ = 4 := by rw [h2]; norm_num
  constructor
  · calc (Real.sqrt 2) ^ 5 = ((Real.sqrt 2) ^ 2) ^ 2 * Real.sqrt 2 := by ring
         _ = 4 * Real.sqrt 2 := by rw [h2]; norm_num
  constructor
  · calc (Real.sqrt 2) ^ 6 = ((Real.sqrt 2) ^ 2) ^ 3 := by ring
         _ = 8 := by rw [h2]; norm_num
  constructor
  · calc (Real.sqrt 2) ^ 7 = ((Real.sqrt 2) ^ 2) ^ 3 * Real.sqrt 2 := by ring
         _ = 8 * Real.sqrt 2 := by rw [h2]; norm_num
  constructor
  · calc (Real.sqrt 2) ^ 8 = ((Real.sqrt 2) ^ 2) ^ 4 := by ring
         _ = 16 := by rw [h2]; norm_num
  constructor
  · calc (Real.sqrt 2) ^ 9 = ((Real.sqrt 2) ^ 2) ^ 4 * Real.sqrt 2 := by ring
         _ = 16 * Real.sqrt 2 := by rw [h2]; norm_num
  constructor
  · calc (Real.sqrt 2) ^ 10 = ((Real.sqrt 2) ^ 2) ^ 5 := by ring
         _ = 32 := by rw [h2]; norm_num
  constructor
  · calc (Real.sqrt 2) ^ 11 = ((Real.sqrt 2) ^ 2) ^ 5 * Real.sqrt 2 := by ring
         _ = 32 * Real.sqrt 2 := by rw [h2]; norm_num
  constructor
  · calc (Real.sqrt 2) ^ 12 = ((Real.sqrt 2) ^ 2) ^ 6 := by ring
         _ = 64 := by rw [h2]; norm_num
  constructor
  · calc (Real.sqrt 2) ^ 13 = ((Real.sqrt 2) ^ 2) ^ 6 * Real.sqrt 2 := by ring
         _ = 64 * Real.sqrt 2 := by rw [h2]; norm_num
  · calc (Real.sqrt 2) ^ 14 = ((Real.sqrt 2) ^ 2) ^ 7 := by ring
         _ = 128 := by rw [h2]; norm_num

lemma sin_sqrt_two_half_tight :
    (649636939 : ℝ) / 1000000000 ≤ Real.sin (Real.sqrt 2 / 2) ∧
      Real.sin (Real.sqrt 2 / 2) ≤ (6496369391 : ℝ) / 10000000000 := by
  have hr := sqrt_two_tight
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hx : Real.sqrt 2 / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · linarith [hr.2]
  have h := abs_sin_sub_sinTaylor13_le (upper := (1 : ℝ)) one_pos hx
  have hp := sqrt_two_powers
  dsimp at hp
  rcases hp with ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  rw [abs_le] at h
  norm_num [sinTaylor13, h3, h5, h7, h9, h11, h13, h14] at h ⊢
  constructor <;> nlinarith [hr.1, hr.2, h.1, h.2]

lemma cos_sqrt_two_half_tight :
    (760244597 : ℝ) / 1000000000 ≤ Real.cos (Real.sqrt 2 / 2) ∧
      Real.cos (Real.sqrt 2 / 2) ≤ (7602445971 : ℝ) / 10000000000 := by
  have hr := sqrt_two_tight
  have hx : Real.sqrt 2 / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · linarith [hr.2]
  have h := abs_cos_sub_cosTaylor12_le (upper := (1 : ℝ)) one_pos hx
  have hp := sqrt_two_powers
  dsimp at hp
  rcases hp with ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  rw [abs_le] at h
  norm_num [cosTaylor12, h2, h4, h6, h8, h10, h12, h13] at h ⊢
  constructor <;> nlinarith [hr.1, hr.2, h.1, h.2]

/-! ## The rational final inequality after periodic cancellation -/

def periodicCorrection : ℝ :=
  (3322500 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (4 * Real.pi ^ 2)) +
  (-7609135 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (16 * Real.pi ^ 2)) +
  (1190194 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (36 * Real.pi ^ 2)) +
  (-731476 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (64 * Real.pi ^ 2)) +
  (-1680572 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (100 * Real.pi ^ 2)) +
  (1141360 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (144 * Real.pi ^ 2))

lemma periodicCorrection_upper :
    periodicCorrection ≤ (368534100 : ℝ) / 10000000000000 := by
  have hp0 : 0 < Real.pi := Real.pi_pos
  have hp := TranscendentalBounds.pi_rational_bounds.2.le
  unfold periodicCorrection
  have hp2 : Real.pi ^ 2 ≤
      ((314159265358979323847 : ℝ) / 10 ^ 20) ^ 2 := by nlinarith
  have hden (n : ℕ) (hn : 0 < n) :
      1 / ((n : ℝ) * ((314159265358979323847 : ℝ) / 10 ^ 20) ^ 2) ≤
        1 / ((n : ℝ) * Real.pi ^ 2) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact mul_le_mul_of_nonneg_left hp2 (by positivity)
  norm_num at hp2 ⊢
  have h4 := hden 4 (by norm_num)
  have h16 := hden 16 (by norm_num)
  have h36 := hden 36 (by norm_num)
  have h64 := hden 64 (by norm_num)
  have h100 := hden 100 (by norm_num)
  have h144 := hden 144 (by norm_num)
  norm_num at h4 h16 h36 h64 h100 h144
  nlinarith

/-- This is the entire nontrivial numeric inequality left after the exact
periodic-frequency cancellation. -/
theorem compact_numeric_inequality :
    Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) *
          Real.cos (Real.sqrt 2 / 2) + periodicCorrection ≤
      (1655086 / 1000000 : ℝ) * Real.sin (Real.sqrt 2 / 2) ^ 2 := by
  have hr := sqrt_two_tight
  have hs := sin_sqrt_two_half_tight
  have hc := cos_sqrt_two_half_tight
  have hP := periodicCorrection_upper
  have hs0 : 0 ≤ Real.sin (Real.sqrt 2 / 2) := by linarith [hs.1]
  have hc0 : 0 ≤ Real.cos (Real.sqrt 2 / 2) := by linarith [hc.1]
  calc
    Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) *
          Real.cos (Real.sqrt 2 / 2) + periodicCorrection ≤
        ((3535533906 : ℝ) / 2500000000) *
          ((6496369391 : ℝ) / 10000000000) *
          ((7602445971 : ℝ) / 10000000000) +
          (368534100 : ℝ) / 10000000000000 := by
            gcongr
            · exact hr.2
            · exact hs.2
            · exact hc.2
    _ ≤ (1655086 / 1000000 : ℝ) *
          ((649636939 : ℝ) / 1000000000) ^ 2 := by norm_num
    _ ≤ (1655086 / 1000000 : ℝ) * Real.sin (Real.sqrt 2 / 2) ^ 2 := by
      gcongr
      exact hs.1

end Zeta23Ext.CurrentWindowClosedHCertificate

end
