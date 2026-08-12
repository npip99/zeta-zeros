/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentKernelTotalDerivatives
import Zeta23Ext.TranscendentalBounds

/-!
# Checked total sinc jets near the removable point

The ordinary production jet checker uses quotient formulas on cells bounded
away from zero.  This module handles the complementary case.  It derives
pole-free enclosures from the degree-seven sine and degree-eight cosine
Taylor bounds, and states the result directly for the total derivatives.
-/

noncomputable section

open Real Set

namespace Zeta23Ext.NearZeroTotalSincJet

open CurrentKernelTotalDerivatives
open SincDerivativeCertificate

def valuePolynomial (x : ℝ) : ℝ :=
  1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040

def firstPolynomial (x : ℝ) : ℝ :=
  -x / 3 + x ^ 3 / 30 - x ^ 5 / 840 + x ^ 7 / 40320

def secondPolynomial (x : ℝ) : ℝ :=
  -(1 / 3) + x ^ 2 / 10 - x ^ 4 / 168 + x ^ 6 / 6720

def valueErrorQ (r : ℚ) : ℚ :=
  r ^ 2 / 6 + r ^ 4 / 120 + r ^ 6 / 5040 + r ^ 7 / 5040

def firstErrorQ (r : ℚ) : ℚ :=
  r / 3 + r ^ 3 / 30 + r ^ 5 / 840 + r ^ 7 / 40320 +
    r ^ 6 / 5040 + r ^ 8 / 40320

def secondErrorQ (r : ℚ) : ℚ :=
  r ^ 2 / 10 + r ^ 4 / 168 + r ^ 6 / 6720 +
    r ^ 5 / 2520 + r ^ 7 / 20160

def valueErrorR (r : ℝ) : ℝ :=
  r ^ 2 / 6 + r ^ 4 / 120 + r ^ 6 / 5040 + r ^ 7 / 5040
def firstErrorR (r : ℝ) : ℝ :=
  r / 3 + r ^ 3 / 30 + r ^ 5 / 840 + r ^ 7 / 40320 +
    r ^ 6 / 5040 + r ^ 8 / 40320
def secondErrorR (r : ℝ) : ℝ :=
  r ^ 2 / 10 + r ^ 4 / 168 + r ^ 6 / 6720 +
    r ^ 5 / 2520 + r ^ 7 / 20160

/-- A rational error budget for a symmetric cell `[-radius,radius]`. -/
structure Witness where
  radius : ℚ
  valueError : ℚ
  firstError : ℚ
  secondError : ℚ

def Witness.check (w : Witness) : Bool :=
  decide (0 ≤ w.radius ∧ w.radius ≤ 1 ∧
    valueErrorQ w.radius ≤ w.valueError ∧
    firstErrorQ w.radius ≤ w.firstError ∧
    secondErrorQ w.radius ≤ w.secondError)

private lemma check_facts {w : Witness} (h : w.check = true) :
    0 ≤ w.radius ∧ w.radius ≤ 1 ∧
      valueErrorQ w.radius ≤ w.valueError ∧
      firstErrorQ w.radius ≤ w.firstError ∧
      secondErrorQ w.radius ≤ w.secondError := by
  simpa [Witness.check] using of_decide_eq_true h

private lemma abs_valuePolynomial_sub_one_le (x : ℝ) :
    |valuePolynomial x - 1| ≤ x ^ 2 / 6 + x ^ 4 / 120 + x ^ 6 / 5040 := by
  rw [show valuePolynomial x - 1 =
      -(x ^ 2 / 6) + x ^ 4 / 120 + -(x ^ 6 / 5040) by
        unfold valuePolynomial; ring]
  calc
    |-(x ^ 2 / 6) + x ^ 4 / 120 + -(x ^ 6 / 5040)| ≤
        |-(x ^ 2 / 6)| + |x ^ 4 / 120| + |-(x ^ 6 / 5040)| := by
      calc
        _ ≤ |-(x ^ 2 / 6) + x ^ 4 / 120| + |-(x ^ 6 / 5040)| :=
          abs_add_le _ _
        _ ≤ (|-(x ^ 2 / 6)| + |x ^ 4 / 120|) + |-(x ^ 6 / 5040)| := by
          gcongr
          exact abs_add_le _ _
    _ = x ^ 2 / 6 + x ^ 4 / 120 + x ^ 6 / 5040 := by
      simp only [abs_neg]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2 / 6),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4 / 120),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 6 / 5040)]

private lemma abs_firstPolynomial_le (x : ℝ) (hx : 0 ≤ x) :
    |firstPolynomial x| ≤
      x / 3 + x ^ 3 / 30 + x ^ 5 / 840 + x ^ 7 / 40320 := by
  rw [show firstPolynomial x =
      -(x / 3) + x ^ 3 / 30 + -(x ^ 5 / 840) + x ^ 7 / 40320 by
        unfold firstPolynomial; ring]
  calc
    |-(x / 3) + x ^ 3 / 30 + -(x ^ 5 / 840) + x ^ 7 / 40320| ≤
        |-(x / 3)| + |x ^ 3 / 30| + |-(x ^ 5 / 840)| +
          |x ^ 7 / 40320| := by
      calc
        _ ≤ |-(x / 3) + x ^ 3 / 30 + -(x ^ 5 / 840)| +
            |x ^ 7 / 40320| := abs_add_le _ _
        _ ≤ (|-(x / 3) + x ^ 3 / 30| + |-(x ^ 5 / 840)|) +
            |x ^ 7 / 40320| := by gcongr; exact abs_add_le _ _
        _ ≤ ((|-(x / 3)| + |x ^ 3 / 30|) + |-(x ^ 5 / 840)|) +
            |x ^ 7 / 40320| := by gcongr; exact abs_add_le _ _
    _ = x / 3 + x ^ 3 / 30 + x ^ 5 / 840 + x ^ 7 / 40320 := by
      simp only [abs_neg]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ x / 3),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 3 / 30),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 5 / 840),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 7 / 40320)]

private lemma abs_secondPolynomial_add_third_le (x : ℝ) :
    |secondPolynomial x + 1 / 3| ≤
      x ^ 2 / 10 + x ^ 4 / 168 + x ^ 6 / 6720 := by
  rw [show secondPolynomial x + 1 / 3 =
      x ^ 2 / 10 + -(x ^ 4 / 168) + x ^ 6 / 6720 by
        unfold secondPolynomial; ring]
  calc
    |x ^ 2 / 10 + -(x ^ 4 / 168) + x ^ 6 / 6720| ≤
        |x ^ 2 / 10| + |-(x ^ 4 / 168)| + |x ^ 6 / 6720| := by
      calc
        _ ≤ |x ^ 2 / 10 + -(x ^ 4 / 168)| + |x ^ 6 / 6720| :=
          abs_add_le _ _
        _ ≤ (|x ^ 2 / 10| + |-(x ^ 4 / 168)|) + |x ^ 6 / 6720| := by
          gcongr
          exact abs_add_le _ _
    _ = x ^ 2 / 10 + x ^ 4 / 168 + x ^ 6 / 6720 := by
      simp only [abs_neg]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2 / 10),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4 / 168),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 6 / 6720)]

private lemma value_approx_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sinc x - valuePolynomial x| ≤ x ^ 7 / 5040 := by
  by_cases hx0 : x = 0
  · subst x
    norm_num [valuePolynomial]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hs := TranscendentalBounds.abs_sin_sub_sinTaylor7_le
      (upper := (1 : ℝ)) one_pos ⟨hx, hx1⟩
    rw [Real.sinc_of_ne_zero hx0]
    have heq : Real.sin x / x - valuePolynomial x =
        (Real.sin x - TranscendentalBounds.sinTaylor7 x) / x := by
      field_simp [hx0]
      unfold valuePolynomial TranscendentalBounds.sinTaylor7
      ring
    rw [heq, abs_div, abs_of_pos hxp]
    calc
      |Real.sin x - TranscendentalBounds.sinTaylor7 x| / x ≤
          (x ^ 8 / 5040) / x := div_le_div_of_nonneg_right hs hxp.le
      _ = x ^ 7 / 5040 := by field_simp [hx0]

private lemma first_approx_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    |sincD1Total x - firstPolynomial x| ≤
      x ^ 6 / 5040 + x ^ 8 / 40320 := by
  by_cases hx0 : x = 0
  · subst x
    norm_num [firstPolynomial]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hs := TranscendentalBounds.abs_sin_sub_sinTaylor7_le
      (upper := (1 : ℝ)) one_pos ⟨hx, hx1⟩
    have hc := TranscendentalBounds.abs_cos_sub_cosTaylor8_le
      (upper := (1 : ℝ)) one_pos ⟨hx, hx1⟩
    rw [sincD1Total_eq hx0]
    have heq : sincD1 x - firstPolynomial x =
        (x * (Real.cos x - TranscendentalBounds.cosTaylor8 x) -
          (Real.sin x - TranscendentalBounds.sinTaylor7 x)) / x ^ 2 := by
      unfold sincD1 firstPolynomial TranscendentalBounds.sinTaylor7
        TranscendentalBounds.cosTaylor8
      field_simp [hx0]
      ring
    rw [heq, abs_div, abs_pow, abs_of_pos hxp]
    have hnum : |x * (Real.cos x - TranscendentalBounds.cosTaylor8 x) -
        (Real.sin x - TranscendentalBounds.sinTaylor7 x)| ≤
        x * (x ^ 9 / 40320) + x ^ 8 / 5040 := by
      calc
        _ ≤ |x * (Real.cos x - TranscendentalBounds.cosTaylor8 x)| +
            |Real.sin x - TranscendentalBounds.sinTaylor7 x| := abs_sub _ _
        _ = x * |Real.cos x - TranscendentalBounds.cosTaylor8 x| +
            |Real.sin x - TranscendentalBounds.sinTaylor7 x| := by
              rw [abs_mul, abs_of_nonneg hx]
        _ ≤ x * (x ^ 9 / 40320) + x ^ 8 / 5040 := by gcongr
    calc
      _ ≤ (x * (x ^ 9 / 40320) + x ^ 8 / 5040) / x ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg x)
      _ = x ^ 6 / 5040 + x ^ 8 / 40320 := by field_simp [hx0]; ring

private lemma second_approx_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    |sincD2Total x - secondPolynomial x| ≤
      x ^ 5 / 2520 + x ^ 7 / 20160 := by
  by_cases hx0 : x = 0
  · subst x
    norm_num [secondPolynomial]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hs := TranscendentalBounds.abs_sin_sub_sinTaylor7_le
      (upper := (1 : ℝ)) one_pos ⟨hx, hx1⟩
    have hc := TranscendentalBounds.abs_cos_sub_cosTaylor8_le
      (upper := (1 : ℝ)) one_pos ⟨hx, hx1⟩
    rw [sincD2Total_eq hx0]
    have heq : sincD2 x - secondPolynomial x =
        ((2 - x ^ 2) *
            (Real.sin x - TranscendentalBounds.sinTaylor7 x) -
          2 * x * (Real.cos x - TranscendentalBounds.cosTaylor8 x)) / x ^ 3 := by
      unfold sincD2 secondNumerator secondPolynomial
        TranscendentalBounds.sinTaylor7 TranscendentalBounds.cosTaylor8
      field_simp [hx0]
      ring
    rw [heq, abs_div, abs_pow, abs_of_pos hxp]
    have hcoef : |2 - x ^ 2| ≤ 2 := by
      rw [abs_of_nonneg (by nlinarith [sq_nonneg x])]
      nlinarith [sq_nonneg x]
    have hnum : |(2 - x ^ 2) *
          (Real.sin x - TranscendentalBounds.sinTaylor7 x) -
        2 * x * (Real.cos x - TranscendentalBounds.cosTaylor8 x)| ≤
        2 * (x ^ 8 / 5040) + 2 * x * (x ^ 9 / 40320) := by
      calc
        _ ≤ |(2 - x ^ 2) *
              (Real.sin x - TranscendentalBounds.sinTaylor7 x)| +
            |2 * x * (Real.cos x - TranscendentalBounds.cosTaylor8 x)| :=
              abs_sub _ _
        _ = |2 - x ^ 2| *
              |Real.sin x - TranscendentalBounds.sinTaylor7 x| +
            (2 * x) * |Real.cos x - TranscendentalBounds.cosTaylor8 x| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hx]
              norm_num
        _ ≤ 2 * (x ^ 8 / 5040) + 2 * x * (x ^ 9 / 40320) := by gcongr
    calc
      _ ≤ (2 * (x ^ 8 / 5040) + 2 * x * (x ^ 9 / 40320)) / x ^ 3 :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = x ^ 5 / 2520 + x ^ 7 / 20160 := by field_simp [hx0]; ring

private lemma nonnegative_bounds {r x : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : x ∈ Icc 0 r) :
    |Real.sinc x - 1| ≤ valueErrorR r ∧
    |sincD1Total x| ≤ firstErrorR r ∧
    |sincD2Total x + 1 / 3| ≤ secondErrorR r := by
  have hx1 : x ≤ 1 := hx.2.trans hr1
  have hv := value_approx_nonneg hx.1 hx1
  have hf := first_approx_nonneg hx.1 hx1
  have hs := second_approx_nonneg hx.1 hx1
  constructor
  · calc
      |Real.sinc x - 1| ≤ |Real.sinc x - valuePolynomial x| +
          |valuePolynomial x - 1| := abs_sub_le _ _ _
      _ ≤ x ^ 7 / 5040 +
          (x ^ 2 / 6 + x ^ 4 / 120 + x ^ 6 / 5040) :=
            add_le_add hv (abs_valuePolynomial_sub_one_le x)
      _ ≤ r ^ 7 / 5040 +
          (r ^ 2 / 6 + r ^ 4 / 120 + r ^ 6 / 5040) := by
            gcongr <;> first | exact hx.1 | exact hx.2
      _ = valueErrorR r := by unfold valueErrorR; ring
  constructor
  · calc
      |sincD1Total x| ≤ |sincD1Total x - firstPolynomial x| +
          |firstPolynomial x| := by
            simpa only [sub_add_cancel] using
              (abs_add_le (sincD1Total x - firstPolynomial x) (firstPolynomial x))
      _ ≤ (x ^ 6 / 5040 + x ^ 8 / 40320) +
          (x / 3 + x ^ 3 / 30 + x ^ 5 / 840 + x ^ 7 / 40320) :=
            add_le_add hf (abs_firstPolynomial_le x hx.1)
      _ ≤ (r ^ 6 / 5040 + r ^ 8 / 40320) +
          (r / 3 + r ^ 3 / 30 + r ^ 5 / 840 + r ^ 7 / 40320) := by
            gcongr <;> first | exact hx.1 | exact hx.2
      _ = firstErrorR r := by unfold firstErrorR; ring
  · calc
      |sincD2Total x + 1 / 3| ≤
          |sincD2Total x - secondPolynomial x| +
            |secondPolynomial x + 1 / 3| := by
              rw [show sincD2Total x + 1 / 3 =
                (sincD2Total x - secondPolynomial x) +
                  (secondPolynomial x + 1 / 3) by ring]
              exact abs_add_le (sincD2Total x - secondPolynomial x)
                (secondPolynomial x + 1 / 3)
      _ ≤ (x ^ 5 / 2520 + x ^ 7 / 20160) +
          (x ^ 2 / 10 + x ^ 4 / 168 + x ^ 6 / 6720) :=
            add_le_add hs (abs_secondPolynomial_add_third_le x)
      _ ≤ (r ^ 5 / 2520 + r ^ 7 / 20160) +
          (r ^ 2 / 10 + r ^ 4 / 168 + r ^ 6 / 6720) := by
            gcongr <;> first | exact hx.1 | exact hx.2
      _ = secondErrorR r := by unfold secondErrorR; ring

private lemma sinc_abs (x : ℝ) : Real.sinc |x| = Real.sinc x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, Real.sinc_neg]

private lemma abs_sincD1Total_abs (x : ℝ) :
    |sincD1Total (|x|)| = |sincD1Total x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx]
    by_cases hx0 : x = 0
    · subst x; simp
    · rw [sincD1Total_eq (neg_ne_zero.mpr hx0), sincD1Total_eq hx0]
      have hneg : sincD1 (-x) = -sincD1 x := by
        unfold sincD1
        rw [Real.cos_neg, Real.sin_neg]
        ring
      rw [hneg, abs_neg]

private lemma sincD2Total_abs (x : ℝ) : sincD2Total |x| = sincD2Total x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx]
    by_cases hx0 : x = 0
    · subst x; simp
    · rw [sincD2Total_eq (neg_ne_zero.mpr hx0), sincD2Total_eq hx0]
      unfold sincD2 secondNumerator
      rw [Real.cos_neg, Real.sin_neg]
      ring

/-- Checked near-zero data bounds the true total sinc jet on the entire
symmetric cell, including the removable point itself. -/
theorem Witness.sound {w : Witness} (h : w.check = true) {x : ℝ}
    (hx : |x| ≤ (w.radius : ℝ)) :
    |Real.sinc x - 1| ≤ (w.valueError : ℝ) ∧
    |sincD1Total x| ≤ (w.firstError : ℝ) ∧
    |sincD2Total x + 1 / 3| ≤ (w.secondError : ℝ) := by
  have hf := check_facts h
  have hr : (0 : ℝ) ≤ w.radius := by exact_mod_cast hf.1
  have hr1 : (w.radius : ℝ) ≤ 1 := by exact_mod_cast hf.2.1
  have hz := nonnegative_bounds hr hr1 ⟨abs_nonneg x, hx⟩
  have hcastValue : valueErrorR (w.radius : ℝ) =
      (valueErrorQ w.radius : ℝ) := by simp [valueErrorR, valueErrorQ]
  have hcastFirst : firstErrorR (w.radius : ℝ) =
      (firstErrorQ w.radius : ℝ) := by simp [firstErrorR, firstErrorQ]
  have hcastSecond : secondErrorR (w.radius : ℝ) =
      (secondErrorQ w.radius : ℝ) := by simp [secondErrorR, secondErrorQ]
  have hev : valueErrorR (w.radius : ℝ) ≤ w.valueError := by
    rw [hcastValue]
    exact_mod_cast hf.2.2.1
  have hef : firstErrorR (w.radius : ℝ) ≤ w.firstError := by
    rw [hcastFirst]
    exact_mod_cast hf.2.2.2.1
  have hes : secondErrorR (w.radius : ℝ) ≤ w.secondError := by
    rw [hcastSecond]
    exact_mod_cast hf.2.2.2.2
  rw [sinc_abs] at hz
  rw [abs_sincD1Total_abs] at hz
  rw [sincD2Total_abs] at hz
  exact ⟨hz.1.trans hev, hz.2.1.trans hef, hz.2.2.trans hes⟩

/-! A compact radius large enough for either grid cell adjacent to every
periodic removable point (`pi / 4000 < 1 / 1000`). -/

def productionWitness : Witness :=
  ⟨1 / 1000, 1 / 5000000, 1 / 2999, 1 / 9999999⟩

theorem productionWitness_checked : productionWitness.check = true := by
  norm_num [productionWitness, Witness.check, valueErrorQ, firstErrorQ,
    secondErrorQ]

theorem production_radius_covers_pi_grid : Real.pi / 4000 < (1 / 1000 : ℝ) := by
  nlinarith [Real.pi_lt_four]

/-- Every periodic minus argument in either grid cell adjacent to its
removable point lies in the checked symmetric series cell. -/
theorem production_periodic_argument_mem {k : ℕ} {x : ℝ}
    (hx : |x - k| ≤ (1 / 4000 : ℝ)) :
    |(2 * Real.pi * k - 2 * Real.pi * x) / 2| ≤ (1 / 1000 : ℝ) := by
  rw [show (2 * Real.pi * k - 2 * Real.pi * x) / 2 =
      Real.pi * ((k : ℝ) - x) by ring, abs_mul, abs_of_pos Real.pi_pos,
    abs_sub_comm]
  calc
    Real.pi * |x - (k : ℝ)| ≤ Real.pi * (1 / 4000 : ℝ) :=
      mul_le_mul_of_nonneg_left hx Real.pi_pos.le
    _ ≤ 1 / 1000 := by
      have hp := production_radius_covers_pi_grid
      simpa [div_eq_mul_inv] using hp.le

/-- Direct total-jet semantics for a periodic argument in either of the
twelve removable-point production cells. -/
theorem production_periodic_total_jet {k : ℕ} {x : ℝ}
    (hx : |x - k| ≤ (1 / 4000 : ℝ)) :
    |Real.sinc ((2 * Real.pi * k - 2 * Real.pi * x) / 2) - 1| ≤
        (productionWitness.valueError : ℝ) ∧
    |sincD1Total ((2 * Real.pi * k - 2 * Real.pi * x) / 2)| ≤
        (productionWitness.firstError : ℝ) ∧
    |sincD2Total ((2 * Real.pi * k - 2 * Real.pi * x) / 2) + 1 / 3| ≤
        (productionWitness.secondError : ℝ) :=
  productionWitness.sound productionWitness_checked
    (by simpa [productionWitness] using production_periodic_argument_mem hx)

end Zeta23Ext.NearZeroTotalSincJet
end
