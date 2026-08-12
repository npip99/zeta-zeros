/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.RationalTrigCell

/-!
# Checked derivative bounds for sinc away from its removable point

The production tangent certificate needs first- and second-derivative bounds
for the seven-term sinc kernel.  Mathlib currently supplies continuity of
`Real.sinc`, but no derivative API.  This file proves the closed derivative
identities away from zero and gives a compact rational witness for a lower
bound on the second derivative over a positive cell.

The key error estimate is sharper than evaluating the quotient formula by
naive interval arithmetic.  Its numerator

`N(x) = (2 - x^2) sin x - 2x cos x`

has derivative exactly `-x^2 cos x`, hence is `upper^2`-Lipschitz on
`[0, upper]`.  A witness evaluates `N` at a nearby rational point using the
existing rational sine/cosine checker and pays only this Lipschitz loss.
-/

noncomputable section

open Real Set Filter Topology

namespace Zeta23Ext.SincDerivativeCertificate

/-- Closed first derivative of sinc away from zero. -/
def sincD1 (x : ℝ) : ℝ :=
  (x * Real.cos x - Real.sin x) / x ^ 2

/-- Numerator of the closed second derivative. -/
def secondNumerator (x : ℝ) : ℝ :=
  (2 - x ^ 2) * Real.sin x - 2 * x * Real.cos x

/-- Closed second derivative of sinc away from zero. -/
def sincD2 (x : ℝ) : ℝ :=
  secondNumerator x / x ^ 3

theorem hasDerivAt_sinc {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt Real.sinc (sincD1 x) x := by
  have heventually : Real.sinc =ᶠ[𝓝 x] fun y => Real.sin y / y := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact Real.sinc_of_ne_zero hy
  have hquotient := (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx
  simp only [id_eq, mul_one] at hquotient
  have hclosed : (Real.cos x * x - Real.sin x) / x ^ 2 = sincD1 x := by
    unfold sincD1
    ring
  rw [hclosed] at hquotient
  exact hquotient.congr_of_eventuallyEq heventually

theorem deriv_sinc {x : ℝ} (hx : x ≠ 0) :
    deriv Real.sinc x = sincD1 x :=
  (hasDerivAt_sinc hx).deriv

theorem hasDerivAt_sincD1 {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt sincD1 (sincD2 x) x := by
  have hraw := (((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)).sub
    (Real.hasDerivAt_sin x)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx)
  have hfun : sincD1 = fun y : ℝ => (y * Real.cos y - Real.sin y) / y ^ 2 := by
    funext y
    rfl
  rw [hfun]
  have hderiv :
      ((1 * Real.cos x + x * -Real.sin x - Real.cos x) * x ^ 2 -
        (x * Real.cos x - Real.sin x) * (2 * x)) / (x ^ 2) ^ 2 = sincD2 x := by
    unfold sincD2 secondNumerator
    field_simp [hx]
    ring
  have hraw' := hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by rfl :
      (fun y : ℝ => (y * Real.cos y - Real.sin y) / y ^ 2) =ᶠ[𝓝 x]
        ((id * Real.cos - Real.sin) / fun y : ℝ => y ^ 2))
  apply hraw'.congr_deriv
  simp only [id_eq, Nat.reduceSubDiff, pow_one, Pi.sub_apply, Pi.mul_apply]
  unfold sincD2 secondNumerator
  field_simp [hx]
  ring

theorem hasDerivAt_secondNumerator (x : ℝ) :
    HasDerivAt secondNumerator (-(x ^ 2) * Real.cos x) x := by
  have hraw := (((hasDerivAt_const x 2).sub (hasDerivAt_pow 2 x)).mul
    (Real.hasDerivAt_sin x)).sub
      (((hasDerivAt_const x 2).mul (hasDerivAt_id x)).mul
        (Real.hasDerivAt_cos x))
  have hfun : secondNumerator = fun y : ℝ =>
      (2 - y ^ 2) * Real.sin y - 2 * y * Real.cos y := rfl
  rw [hfun]
  have hderiv :
      (0 - 2 * x) * Real.sin x + (2 - x ^ 2) * Real.cos x -
        ((0 * x + 2 * 1) * Real.cos x + (2 * x) * -Real.sin x) =
          -(x ^ 2) * Real.cos x := by
    ring
  have hraw' := hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by rfl :
      (fun y : ℝ => (2 - y ^ 2) * Real.sin y - 2 * y * Real.cos y) =ᶠ[𝓝 x]
        (((fun y : ℝ => 2) - fun y => y ^ 2) * Real.sin -
          (fun y : ℝ => 2) * id * Real.cos))
  apply hraw'.congr_deriv
  simp only [id_eq, Nat.reduceSubDiff, pow_one, Pi.sub_apply, Pi.mul_apply]
  ring

lemma abs_deriv_secondNumerator_le {upper x : ℝ}
    (hupper : 0 ≤ upper) (hx : x ∈ Icc 0 upper) :
    |deriv secondNumerator x| ≤ upper ^ 2 := by
  rw [(hasDerivAt_secondNumerator x).deriv, abs_mul, abs_neg,
    abs_of_nonneg (sq_nonneg x)]
  calc
    x ^ 2 * |Real.cos x| ≤ x ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (sq_nonneg x)
    _ ≤ upper ^ 2 := by nlinarith [hx.1, hx.2]

/-- Sharp numerator transport from a rational center to a positive cell. -/
theorem abs_secondNumerator_sub_le {q radius upper x : ℝ}
    (hupper : 0 ≤ upper) (hq : q ∈ Icc 0 upper) (hx : x ∈ Icc 0 upper)
    (hcell : |x - q| ≤ radius) :
    |secondNumerator x - secondNumerator q| ≤ upper ^ 2 * radius := by
  have hlip := (convex_Icc (0 : ℝ) upper).norm_image_sub_le_of_norm_deriv_le
    (f := secondNumerator) (x := q) (y := x) (C := upper ^ 2)
    (fun z _ => (hasDerivAt_secondNumerator z).differentiableAt)
    (fun z hz => by
      simpa only [Real.norm_eq_abs] using abs_deriv_secondNumerator_le hupper hz)
    hq hx
  calc
    |secondNumerator x - secondNumerator q| ≤ upper ^ 2 * |x - q| := by
      simpa only [Real.norm_eq_abs] using hlip
    _ ≤ upper ^ 2 * radius :=
      mul_le_mul_of_nonneg_left hcell (sq_nonneg upper)

/-- Rational approximation used by the second-derivative checker.  The sine
and cosine approximations refer to the *actual rational center* `q`; range
reduction is supplied separately by `RationalTrigCell.Witness`. -/
def numeratorApprox (q sinApprox cosApprox : ℝ) : ℝ :=
  (2 - q ^ 2) * sinApprox - 2 * q * cosApprox

lemma secondNumerator_center_error {q sinApprox cosApprox sinError cosError : ℝ}
    (hs : |Real.sin q - sinApprox| ≤ sinError)
    (hc : |Real.cos q - cosApprox| ≤ cosError) :
    |secondNumerator q - numeratorApprox q sinApprox cosApprox| ≤
      |2 - q ^ 2| * sinError + 2 * |q| * cosError := by
  unfold secondNumerator numeratorApprox
  rw [show (2 - q ^ 2) * Real.sin q - 2 * q * Real.cos q -
      ((2 - q ^ 2) * sinApprox - 2 * q * cosApprox) =
      (2 - q ^ 2) * (Real.sin q - sinApprox) -
        (2 * q) * (Real.cos q - cosApprox) by ring]
  calc
    |(2 - q ^ 2) * (Real.sin q - sinApprox) -
          (2 * q) * (Real.cos q - cosApprox)| ≤
        |(2 - q ^ 2) * (Real.sin q - sinApprox)| +
          |(2 * q) * (Real.cos q - cosApprox)| := abs_sub _ _
    _ = |2 - q ^ 2| * |Real.sin q - sinApprox| +
          2 * |q| * |Real.cos q - cosApprox| := by
          rw [abs_mul, abs_mul, abs_mul]
          norm_num
    _ ≤ |2 - q ^ 2| * sinError + 2 * |q| * cosError := by
      gcongr

/-- Data whose Boolean portion is entirely rational.  The separate trig row
contains its own rational Taylor/remainder checks. -/
structure SecondWitness where
  q : ℚ
  radius : ℚ
  upper : ℚ
  trig : RationalTrigCell.Witness
  lower : ℚ

def SecondWitness.sinApprox (w : SecondWitness) : ℚ :=
  (-1 : ℚ) ^ w.trig.k *
    (w.trig.center - w.trig.center ^ 3 / 6 +
      w.trig.center ^ 5 / 120 - w.trig.center ^ 7 / 5040)

def SecondWitness.cosApprox (w : SecondWitness) : ℚ :=
  (-1 : ℚ) ^ w.trig.k *
    (1 - w.trig.center ^ 2 / 2 + w.trig.center ^ 4 / 24 -
      w.trig.center ^ 6 / 720 + w.trig.center ^ 8 / 40320)

def SecondWitness.error (w : SecondWitness) : ℚ :=
  |2 - w.q ^ 2| * w.trig.err +
    2 * |w.q| * w.trig.err + w.upper ^ 2 * w.radius

def SecondWitness.numeratorApprox (w : SecondWitness) : ℚ :=
  (2 - w.q ^ 2) * w.sinApprox - 2 * w.q * w.cosApprox

def SecondWitness.numeratorLower (w : SecondWitness) : ℚ :=
  w.numeratorApprox - w.error

/-- All purely rational side conditions, including the sign-sensitive
division by the positive cube. -/
def SecondWitness.check (w : SecondWitness) : Bool :=
  RationalTrigCell.check w.trig && RationalTrigCell.cosCheck w.trig &&
    decide (0 < w.q - w.radius ∧ w.q + w.radius ≤ w.upper ∧
      0 ≤ w.radius ∧
      (if 0 ≤ w.lower then
        w.lower * w.upper ^ 3 ≤ w.numeratorLower
      else
        w.lower * (w.q - w.radius) ^ 3 ≤ w.numeratorLower))

lemma SecondWitness.check_sound {w : SecondWitness} (hw : w.check = true) :
    RationalTrigCell.check w.trig = true ∧
      RationalTrigCell.cosCheck w.trig = true ∧
      0 < w.q - w.radius ∧ w.q + w.radius ≤ w.upper ∧
      0 ≤ w.radius ∧
      (if 0 ≤ w.lower then
        w.lower * w.upper ^ 3 ≤ w.numeratorLower
      else
        w.lower * (w.q - w.radius) ^ 3 ≤ w.numeratorLower) := by
  simpa [SecondWitness.check, Bool.and_eq_true, and_assoc] using hw

/-- Soundness of the rational sinc-second-derivative cell witness.  The two
center premises are exactly the conclusions supplied by the checked rational
trig rows (after their `(-1)^k` sign is moved to the approximation).
-/
theorem SecondWitness.lower_sound {w : SecondWitness} (hw : w.check = true)
    (hs : |Real.sin (w.q : ℝ) - (w.sinApprox : ℝ)| ≤ (w.trig.err : ℝ))
    (hc : |Real.cos (w.q : ℝ) - (w.cosApprox : ℝ)| ≤ (w.trig.err : ℝ))
    {x : ℝ} (hcell : |x - (w.q : ℝ)| ≤ (w.radius : ℝ)) :
    (w.lower : ℝ) ≤ sincD2 x := by
  obtain ⟨hsCheck, hcCheck, hpositive, hupper, hradius, hdivide⟩ :=
    SecondWitness.check_sound hw
  have hq0Q : 0 < w.q := by linarith
  have hq0 : 0 < (w.q : ℝ) := by exact_mod_cast hq0Q
  have hxLower : (w.q : ℝ) - w.radius ≤ x := by
    rw [abs_le] at hcell
    linarith [hcell.1]
  have hxUpper : x ≤ (w.q : ℝ) + w.radius := by
    rw [abs_le] at hcell
    linarith [hcell.2]
  have hx0 : 0 < x := by
    have hp : (0 : ℝ) < (w.q : ℝ) - w.radius := by exact_mod_cast hpositive
    linarith
  have hupperR : (w.q : ℝ) + w.radius ≤ w.upper := by exact_mod_cast hupper
  have hqMem : (w.q : ℝ) ∈ Icc 0 (w.upper : ℝ) := by
    constructor
    · exact hq0.le
    · linarith [hupperR]
  have hxMem : x ∈ Icc 0 (w.upper : ℝ) := by
    constructor
    · exact hx0.le
    · linarith [hxUpper, hupperR]
  have hcenter := secondNumerator_center_error hs hc
  have hupperQ : (0 : ℚ) ≤ w.upper := by linarith
  have htransport := abs_secondNumerator_sub_le
    (upper := (w.upper : ℝ)) (q := (w.q : ℝ)) (x := x)
    (by exact_mod_cast hupperQ) hqMem hxMem hcell
  have hApproxCast : (w.numeratorApprox : ℝ) =
      SincDerivativeCertificate.numeratorApprox
        (w.q : ℝ) (w.sinApprox : ℝ) (w.cosApprox : ℝ) := by
    simp only [SecondWitness.numeratorApprox,
      SincDerivativeCertificate.numeratorApprox]
    push_cast
    rfl
  have hErrorCast : (w.error : ℝ) =
      |2 - (w.q : ℝ) ^ 2| * (w.trig.err : ℝ) +
        2 * |(w.q : ℝ)| * (w.trig.err : ℝ) +
          (w.upper : ℝ) ^ 2 * (w.radius : ℝ) := by
    simp only [SecondWitness.error]
    push_cast
    rfl
  have hnLower : (w.numeratorLower : ℝ) ≤ secondNumerator x := by
    have h1 := (neg_le_of_abs_le hcenter)
    have h2 := (neg_le_of_abs_le htransport)
    rw [SecondWitness.numeratorLower]
    push_cast
    rw [hApproxCast, hErrorCast]
    linarith
  have hxCube : 0 < x ^ 3 := pow_pos hx0 3
  rw [sincD2, le_div_iff₀ hxCube]
  apply le_trans _ hnLower
  by_cases hlower : 0 ≤ w.lower
  · simp [hlower] at hdivide
    have hlower0 : (0 : ℝ) ≤ w.lower := by exact_mod_cast hlower
    have hxu : x ^ 3 ≤ (w.upper : ℝ) ^ 3 := by
      gcongr
      exact hxMem.2
    calc
      (w.lower : ℝ) * x ^ 3 ≤ w.lower * (w.upper : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hxu hlower0
      _ ≤ w.numeratorLower := by exact_mod_cast hdivide
  · simp [hlower] at hdivide
    have hlowerNeg : (w.lower : ℝ) < 0 := by
      exact_mod_cast (lt_of_not_ge hlower)
    have hleft0 : (0 : ℝ) ≤ (w.q : ℝ) - w.radius := by
      exact_mod_cast hpositive.le
    have hlx : ((w.q : ℝ) - w.radius) ^ 3 ≤ x ^ 3 := by
      gcongr
    calc
      (w.lower : ℝ) * x ^ 3 ≤ w.lower * ((w.q : ℝ) - w.radius) ^ 3 :=
        mul_le_mul_of_nonpos_left hlx hlowerNeg.le
      _ ≤ w.numeratorLower := by exact_mod_cast hdivide

/-! ## Fully checked regression cell -/

/-- A nonzero sinc-second-derivative cell whose transcendental center
enclosures and all witness arithmetic are checked by Lean. -/
def halfWitness : SecondWitness where
  q := 1 / 2
  radius := 1 / 100
  upper := 1
  trig := ⟨0, 1 / 2, 0, 1, 1 / 1000000⟩
  lower := -1 / 2

theorem halfWitness_checked : halfWitness.check = true := by
  norm_num [halfWitness, SecondWitness.check, RationalTrigCell.check,
    RationalTrigCell.cosCheck, SecondWitness.numeratorLower,
    SecondWitness.numeratorApprox, SecondWitness.error,
    SecondWitness.sinApprox, SecondWitness.cosApprox]

theorem halfWitness_sound {x : ℝ}
    (hcell : |x - (1 / 2 : ℝ)| ≤ 1 / 100) :
    (-1 / 2 : ℝ) ≤ sincD2 x := by
  have hs' : |Real.sin (halfWitness.q : ℝ) -
      (halfWitness.sinApprox : ℝ)| ≤ (halfWitness.trig.err : ℝ) := by
    have hs := RationalTrigCell.sin_sound
      (w := halfWitness.trig) (by
        norm_num [halfWitness, RationalTrigCell.check])
      (x := (1 / 2 : ℝ)) (by norm_num [halfWitness])
    simpa [halfWitness, SecondWitness.sinApprox,
      TranscendentalBounds.sinTaylor7] using hs
  have hc' : |Real.cos (halfWitness.q : ℝ) -
      (halfWitness.cosApprox : ℝ)| ≤ (halfWitness.trig.err : ℝ) := by
    have hc := RationalTrigCell.cos_sound
      (w := halfWitness.trig) (by
        norm_num [halfWitness, RationalTrigCell.cosCheck])
      (x := (1 / 2 : ℝ)) (by norm_num [halfWitness])
    simpa [halfWitness, SecondWitness.cosApprox,
      TranscendentalBounds.cosTaylor8] using hc
  have hsound := SecondWitness.lower_sound halfWitness_checked hs' hc'
    (x := x) (by simpa [halfWitness] using hcell)
  simpa [halfWitness] using hsound

end Zeta23Ext.SincDerivativeCertificate

end
