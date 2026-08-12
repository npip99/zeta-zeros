/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.SincDerivativeCertificate

/-!
# Layered rational certificates for `(sinc,sinc',sinc'')`

Direct interval division loses too much near the production argument `0.296`.
This checker instead bounds the second derivative first, transports the first
derivative with that bound, then transports sinc with the first-derivative
bound.  Every arithmetic side condition is a Boolean decision over rationals.
-/

noncomputable section

open Real Set Filter Topology

namespace Zeta23Ext.SincJetCertificate

open SincDerivativeCertificate

structure Witness where
  q : ℚ
  radius : ℚ
  upper : ℚ
  sinApprox : ℚ
  cosApprox : ℚ
  trigError : ℚ
  valueLower : ℚ
  valueUpper : ℚ
  firstLower : ℚ
  firstUpper : ℚ
  secondLower : ℚ
  secondUpper : ℚ

def Witness.secondApprox (w : Witness) : ℚ :=
  (2 - w.q ^ 2) * w.sinApprox - 2 * w.q * w.cosApprox

def Witness.secondError (w : Witness) : ℚ :=
  |2 - w.q ^ 2| * w.trigError + 2 * |w.q| * w.trigError +
    w.upper ^ 2 * w.radius

def Witness.secondAbs (w : Witness) : ℚ :=
  max |w.secondLower| |w.secondUpper|

def Witness.firstApprox (w : Witness) : ℚ :=
  (w.q * w.cosApprox - w.sinApprox) / w.q ^ 2

def Witness.firstError (w : Witness) : ℚ :=
  (|w.q| * w.trigError + w.trigError) / w.q ^ 2

def Witness.firstAbs (w : Witness) : ℚ :=
  max |w.firstLower| |w.firstUpper|

def Witness.valueApprox (w : Witness) : ℚ := w.sinApprox / w.q
def Witness.valueError (w : Witness) : ℚ := w.trigError / w.q

def Witness.check (w : Witness) : Bool :=
  decide (0 < w.q - w.radius ∧ w.q + w.radius ≤ w.upper ∧
    0 ≤ w.radius ∧ 0 ≤ w.trigError ∧
    w.secondLower ≤ w.secondUpper ∧
    w.firstLower ≤ w.firstUpper ∧ w.valueLower ≤ w.valueUpper ∧
    w.secondLower * (w.q - w.radius) ^ 3 ≤ w.secondApprox - w.secondError ∧
    w.secondLower * (w.q + w.radius) ^ 3 ≤ w.secondApprox - w.secondError ∧
    w.secondApprox + w.secondError ≤
      w.secondUpper * (w.q - w.radius) ^ 3 ∧
    w.secondApprox + w.secondError ≤
      w.secondUpper * (w.q + w.radius) ^ 3 ∧
    w.firstLower + w.secondAbs * w.radius ≤
      w.firstApprox - w.firstError ∧
    w.firstApprox + w.firstError ≤
      w.firstUpper - w.secondAbs * w.radius ∧
    w.valueLower + w.firstAbs * w.radius ≤
      w.valueApprox - w.valueError ∧
    w.valueApprox + w.valueError ≤
      w.valueUpper - w.firstAbs * w.radius)

private lemma check_sound {w : Witness} (hw : w.check = true) :
    0 < w.q - w.radius ∧ w.q + w.radius ≤ w.upper ∧
    0 ≤ w.radius ∧ 0 ≤ w.trigError ∧
    w.secondLower ≤ w.secondUpper ∧
    w.firstLower ≤ w.firstUpper ∧ w.valueLower ≤ w.valueUpper ∧
    w.secondLower * (w.q - w.radius) ^ 3 ≤ w.secondApprox - w.secondError ∧
    w.secondLower * (w.q + w.radius) ^ 3 ≤ w.secondApprox - w.secondError ∧
    w.secondApprox + w.secondError ≤
      w.secondUpper * (w.q - w.radius) ^ 3 ∧
    w.secondApprox + w.secondError ≤
      w.secondUpper * (w.q + w.radius) ^ 3 ∧
    w.firstLower + w.secondAbs * w.radius ≤
      w.firstApprox - w.firstError ∧
    w.firstApprox + w.firstError ≤
      w.firstUpper - w.secondAbs * w.radius ∧
    w.valueLower + w.firstAbs * w.radius ≤
      w.valueApprox - w.valueError ∧
    w.valueApprox + w.valueError ≤
      w.valueUpper - w.firstAbs * w.radius := by
  simpa [Witness.check] using of_decide_eq_true hw

private lemma abs_le_max_abs {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    |x| ≤ max |a| |b| := by
  rw [abs_le]
  constructor
  · have hma : |a| ≤ max |a| |b| := le_max_left _ _
    have haa : -|a| ≤ a := neg_abs_le a
    linarith
  · exact hb.trans ((le_abs_self b).trans (le_max_right _ _))

private lemma second_bounds {w : Witness} (hw : w.check = true)
    (hs : |Real.sin (w.q : ℝ) - (w.sinApprox : ℝ)| ≤ (w.trigError : ℝ))
    (hc : |Real.cos (w.q : ℝ) - (w.cosApprox : ℝ)| ≤ (w.trigError : ℝ))
    {y : ℝ} (hy : |y - (w.q : ℝ)| ≤ (w.radius : ℝ)) :
    (w.secondLower : ℝ) ≤ sincD2 y ∧ sincD2 y ≤ (w.secondUpper : ℝ) := by
  obtain ⟨hpos, hu, hr, _, _, _, _, hlowLo, hlowHi,
    hhighLo, hhighHi, _⟩ := check_sound hw
  have hylo : (w.q : ℝ) - w.radius ≤ y := by
    rw [abs_le] at hy
    linarith [hy.1]
  have hyhi : y ≤ (w.q : ℝ) + w.radius := by
    rw [abs_le] at hy
    linarith [hy.2]
  have hypos : 0 < y := by
    have : (0 : ℝ) < (w.q : ℝ) - w.radius := by exact_mod_cast hpos
    linarith
  have hqmem : (w.q : ℝ) ∈ Icc 0 (w.upper : ℝ) := by
    have hr' : (0 : ℝ) ≤ w.radius := by exact_mod_cast hr
    have hp' : (0 : ℝ) < (w.q : ℝ) - w.radius := by exact_mod_cast hpos
    have hu' : (w.q : ℝ) + w.radius ≤ w.upper := by exact_mod_cast hu
    constructor <;> linarith
  have hymem : y ∈ Icc 0 (w.upper : ℝ) := by
    have hu' : (w.q : ℝ) + w.radius ≤ w.upper := by exact_mod_cast hu
    constructor
    · exact hypos.le
    · linarith
  have hcerror := secondNumerator_center_error hs hc
  have hcerror' : |secondNumerator (w.q : ℝ) - (w.secondApprox : ℝ)| ≤
      |2 - (w.q : ℝ) ^ 2| * w.trigError +
        2 * |(w.q : ℝ)| * w.trigError := by
    convert hcerror using 1
    simp only [Witness.secondApprox,
      SincDerivativeCertificate.numeratorApprox]
    push_cast
    ring
  have ht := abs_secondNumerator_sub_le
    (upper := (w.upper : ℝ)) (q := (w.q : ℝ)) (x := y)
    (by have hr' : (0 : ℝ) ≤ w.radius := by exact_mod_cast hr
        have hp' : (0 : ℝ) < (w.q : ℝ) - w.radius := by exact_mod_cast hpos
        have hu' : (w.q : ℝ) + w.radius ≤ w.upper := by exact_mod_cast hu
        linarith) hqmem hymem hy
  have hn : |secondNumerator y - (w.secondApprox : ℝ)| ≤
      (w.secondError : ℝ) := by
    calc
      |secondNumerator y - (w.secondApprox : ℝ)| ≤
          |secondNumerator y - secondNumerator (w.q : ℝ)| +
            |secondNumerator (w.q : ℝ) - (w.secondApprox : ℝ)| :=
        abs_sub_le _ _ _
      _ ≤ (w.upper : ℝ) ^ 2 * w.radius +
          (|2 - (w.q : ℝ) ^ 2| * w.trigError +
            2 * |(w.q : ℝ)| * w.trigError) := add_le_add ht hcerror'
      _ = (w.secondError : ℝ) := by
        simp only [Witness.secondError]
        push_cast
        ring
  have hnlo : (w.secondApprox : ℝ) - w.secondError ≤ secondNumerator y := by
    linarith [neg_abs_le (secondNumerator y - (w.secondApprox : ℝ)), hn]
  have hnhi : secondNumerator y ≤ (w.secondApprox : ℝ) + w.secondError := by
    linarith [le_abs_self (secondNumerator y - (w.secondApprox : ℝ)), hn]
  have hbase : (0 : ℝ) ≤ (w.q : ℝ) - w.radius := by exact_mod_cast hpos.le
  have hloCube : ((w.q : ℝ) - w.radius) ^ 3 ≤ y ^ 3 := by gcongr
  have hhiCube : y ^ 3 ≤ ((w.q : ℝ) + w.radius) ^ 3 := by gcongr
  have hycube : 0 < y ^ 3 := pow_pos hypos 3
  rw [sincD2]
  constructor
  · rw [le_div_iff₀ hycube]
    by_cases ha : 0 ≤ (w.secondLower : ℝ)
    · have ha : (0 : ℝ) ≤ w.secondLower := by assumption
      have hc : (w.secondLower : ℝ) * y ^ 3 ≤
          w.secondLower * ((w.q : ℝ) + w.radius) ^ 3 :=
        mul_le_mul_of_nonneg_left hhiCube ha
      exact hc.trans ((by exact_mod_cast hlowHi :
        (w.secondLower : ℝ) * ((w.q : ℝ) + w.radius) ^ 3 ≤
          w.secondApprox - w.secondError).trans hnlo)
    · have ha' : (w.secondLower : ℝ) ≤ 0 := le_of_not_ge ha
      have hc : (w.secondLower : ℝ) * y ^ 3 ≤
          w.secondLower * ((w.q : ℝ) - w.radius) ^ 3 :=
        mul_le_mul_of_nonpos_left hloCube ha'
      exact hc.trans ((by exact_mod_cast hlowLo :
        (w.secondLower : ℝ) * ((w.q : ℝ) - w.radius) ^ 3 ≤
          w.secondApprox - w.secondError).trans hnlo)
  · rw [div_le_iff₀ hycube]
    by_cases ha : 0 ≤ (w.secondUpper : ℝ)
    · have ha : (0 : ℝ) ≤ w.secondUpper := by assumption
      have hc : (w.secondUpper : ℝ) * ((w.q : ℝ) - w.radius) ^ 3 ≤
          w.secondUpper * y ^ 3 := mul_le_mul_of_nonneg_left hloCube ha
      exact hnhi.trans ((by exact_mod_cast hhighLo :
        (w.secondApprox : ℝ) + w.secondError ≤
          w.secondUpper * ((w.q : ℝ) - w.radius) ^ 3).trans hc)
    · have ha' : (w.secondUpper : ℝ) ≤ 0 := le_of_not_ge ha
      have hc : (w.secondUpper : ℝ) * ((w.q : ℝ) + w.radius) ^ 3 ≤
          w.secondUpper * y ^ 3 := mul_le_mul_of_nonpos_left hhiCube ha'
      exact hnhi.trans ((by exact_mod_cast hhighHi :
        (w.secondApprox : ℝ) + w.secondError ≤
          w.secondUpper * ((w.q : ℝ) + w.radius) ^ 3).trans hc)

private lemma first_center_error {w : Witness} (hw : w.check = true)
    (hs : |Real.sin (w.q : ℝ) - (w.sinApprox : ℝ)| ≤ (w.trigError : ℝ))
    (hc : |Real.cos (w.q : ℝ) - (w.cosApprox : ℝ)| ≤ (w.trigError : ℝ)) :
    |sincD1 (w.q : ℝ) - (w.firstApprox : ℝ)| ≤ (w.firstError : ℝ) := by
  have hq : (0 : ℝ) < w.q := by
    obtain ⟨hp, _, hr, _⟩ := check_sound hw
    have hp' : (0 : ℝ) < (w.q : ℝ) - w.radius := by exact_mod_cast hp
    have hr' : (0 : ℝ) ≤ w.radius := by exact_mod_cast hr
    linarith
  unfold sincD1 Witness.firstApprox Witness.firstError
  push_cast
  rw [show ((w.q : ℝ) * Real.cos w.q - Real.sin w.q) / (w.q : ℝ) ^ 2 -
      ((w.q : ℝ) * w.cosApprox - w.sinApprox) / (w.q : ℝ) ^ 2 =
      ((w.q : ℝ) * (Real.cos w.q - w.cosApprox) -
        (Real.sin w.q - w.sinApprox)) / (w.q : ℝ) ^ 2 by ring,
    abs_div, abs_pow, abs_of_pos hq]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hq)).2
  calc
    |(w.q : ℝ) * (Real.cos w.q - w.cosApprox) -
        (Real.sin w.q - w.sinApprox)| ≤
      |(w.q : ℝ) * (Real.cos w.q - w.cosApprox)| +
        |Real.sin w.q - w.sinApprox| := abs_sub _ _
    _ = |(w.q : ℝ)| * |Real.cos w.q - w.cosApprox| +
        |Real.sin w.q - w.sinApprox| := by rw [abs_mul]
    _ ≤ |(w.q : ℝ)| * w.trigError + w.trigError := by gcongr
    _ = (w.q : ℝ) * w.trigError + w.trigError := by rw [abs_of_pos hq]

private lemma value_center_error {w : Witness} (hw : w.check = true)
    (hs : |Real.sin (w.q : ℝ) - (w.sinApprox : ℝ)| ≤ (w.trigError : ℝ)) :
    |Real.sinc (w.q : ℝ) - (w.valueApprox : ℝ)| ≤ (w.valueError : ℝ) := by
  have hq : (0 : ℝ) < w.q := by
    obtain ⟨hp, _, hr, _⟩ := check_sound hw
    have hp' : (0 : ℝ) < (w.q : ℝ) - w.radius := by exact_mod_cast hp
    have hr' : (0 : ℝ) ≤ w.radius := by exact_mod_cast hr
    linarith
  rw [Real.sinc_of_ne_zero hq.ne']
  unfold Witness.valueApprox Witness.valueError
  push_cast
  rw [← sub_div, abs_div, abs_of_pos hq]
  exact div_le_div_of_nonneg_right hs hq.le

private lemma cell_facts {w : Witness} (hw : w.check = true) {y : ℝ}
    (hy : |y - (w.q : ℝ)| ≤ (w.radius : ℝ)) :
    0 < y ∧ (w.q : ℝ) ∈ Icc ((w.q : ℝ) - w.radius) (w.q + w.radius) ∧
      y ∈ Icc ((w.q : ℝ) - w.radius) (w.q + w.radius) := by
  obtain ⟨hp, _, hr, _⟩ := check_sound hw
  have hp' : (0 : ℝ) < (w.q : ℝ) - w.radius := by exact_mod_cast hp
  have hr' : (0 : ℝ) ≤ w.radius := by exact_mod_cast hr
  rw [abs_le] at hy
  constructor
  · linarith [hy.1]
  constructor
  · constructor <;> linarith
  · constructor <;> linarith [hy.1, hy.2]

private lemma first_bounds {w : Witness} (hw : w.check = true)
    (hs : |Real.sin (w.q : ℝ) - (w.sinApprox : ℝ)| ≤ (w.trigError : ℝ))
    (hc : |Real.cos (w.q : ℝ) - (w.cosApprox : ℝ)| ≤ (w.trigError : ℝ))
    {y : ℝ} (hy : |y - (w.q : ℝ)| ≤ (w.radius : ℝ)) :
    (w.firstLower : ℝ) ≤ sincD1 y ∧ sincD1 y ≤ (w.firstUpper : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfl, hfu, _⟩ := check_sound hw
  obtain ⟨hypos, hqmem, hymem⟩ := cell_facts hw hy
  have hcenter := first_center_error hw hs hc
  have htransport :=
    (convex_Icc ((w.q : ℝ) - w.radius) (w.q + w.radius)).norm_image_sub_le_of_norm_deriv_le
      (f := sincD1) (x := (w.q : ℝ)) (y := y) (C := (w.secondAbs : ℝ))
      (fun z hz => by
        have hzpos : 0 < z := by
          obtain ⟨hp, _, _, _⟩ := check_sound hw
          have hp' : (0 : ℝ) < (w.q : ℝ) - w.radius := by exact_mod_cast hp
          exact hp'.trans_le hz.1
        exact (hasDerivAt_sincD1 hzpos.ne').differentiableAt)
      (fun z hz => by
        have hzcell : |z - (w.q : ℝ)| ≤ (w.radius : ℝ) := by
          rw [abs_le]
          constructor <;> linarith [hz.1, hz.2]
        have hb := second_bounds hw hs hc hzcell
        have hzpos : 0 < z := (cell_facts hw hzcell).1
        rw [(hasDerivAt_sincD1 hzpos.ne').deriv]
        simpa only [Real.norm_eq_abs, Witness.secondAbs, Rat.cast_max,
          Rat.cast_abs] using abs_le_max_abs hb.1 hb.2)
      hqmem hymem
  have hdiff : |sincD1 y - sincD1 (w.q : ℝ)| ≤
      (w.secondAbs : ℝ) * w.radius := by
    have ht : |sincD1 y - sincD1 (w.q : ℝ)| ≤
        (w.secondAbs : ℝ) * |y - (w.q : ℝ)| := by
      simpa only [Real.norm_eq_abs] using htransport
    have hnonneg : (0 : ℝ) ≤ w.secondAbs := by
      simp only [Witness.secondAbs, Rat.cast_max, Rat.cast_abs]
      exact le_max_of_le_left (abs_nonneg _)
    exact ht.trans (mul_le_mul_of_nonneg_left hy hnonneg)
  have hcenterLo : (w.firstApprox : ℝ) - w.firstError ≤ sincD1 w.q := by
    linarith [neg_abs_le (sincD1 (w.q : ℝ) - w.firstApprox), hcenter]
  have hcenterHi : sincD1 w.q ≤ (w.firstApprox : ℝ) + w.firstError := by
    linarith [le_abs_self (sincD1 (w.q : ℝ) - w.firstApprox), hcenter]
  constructor
  · have hcheck : (w.firstLower : ℝ) + w.secondAbs * w.radius ≤
        w.firstApprox - w.firstError := by exact_mod_cast hfl
    linarith [neg_abs_le (sincD1 y - sincD1 (w.q : ℝ)), hdiff]
  · have hcheck : (w.firstApprox : ℝ) + w.firstError ≤
        w.firstUpper - w.secondAbs * w.radius := by exact_mod_cast hfu
    linarith [le_abs_self (sincD1 y - sincD1 (w.q : ℝ)), hdiff]

/-- Soundness of a checked layered sinc-jet row. -/
theorem Witness.sound {w : Witness} (hw : w.check = true)
    (hs : |Real.sin (w.q : ℝ) - (w.sinApprox : ℝ)| ≤ (w.trigError : ℝ))
    (hc : |Real.cos (w.q : ℝ) - (w.cosApprox : ℝ)| ≤ (w.trigError : ℝ))
    {y : ℝ} (hy : |y - (w.q : ℝ)| ≤ (w.radius : ℝ)) :
    ((w.valueLower : ℝ) ≤ Real.sinc y ∧ Real.sinc y ≤ w.valueUpper) ∧
    ((w.firstLower : ℝ) ≤ sincD1 y ∧ sincD1 y ≤ w.firstUpper) ∧
    ((w.secondLower : ℝ) ≤ sincD2 y ∧ sincD2 y ≤ w.secondUpper) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hvl, hvu⟩ := check_sound hw
  obtain ⟨_, hqmem, hymem⟩ := cell_facts hw hy
  have hsecond := second_bounds hw hs hc hy
  have hfirst := first_bounds hw hs hc hy
  have hcenter := value_center_error hw hs
  have htransport :=
    (convex_Icc ((w.q : ℝ) - w.radius) (w.q + w.radius)).norm_image_sub_le_of_norm_deriv_le
      (f := Real.sinc) (x := (w.q : ℝ)) (y := y) (C := (w.firstAbs : ℝ))
      (fun z hz => by
        have hzcell : |z - (w.q : ℝ)| ≤ (w.radius : ℝ) := by
          rw [abs_le]
          constructor <;> linarith [hz.1, hz.2]
        exact (hasDerivAt_sinc (cell_facts hw hzcell).1.ne').differentiableAt)
      (fun z hz => by
        have hzcell : |z - (w.q : ℝ)| ≤ (w.radius : ℝ) := by
          rw [abs_le]
          constructor <;> linarith [hz.1, hz.2]
        have hb := first_bounds hw hs hc hzcell
        rw [(hasDerivAt_sinc (cell_facts hw hzcell).1.ne').deriv]
        simpa only [Real.norm_eq_abs, Witness.firstAbs, Rat.cast_max,
          Rat.cast_abs] using abs_le_max_abs hb.1 hb.2)
      hqmem hymem
  have hdiff : |Real.sinc y - Real.sinc (w.q : ℝ)| ≤
      (w.firstAbs : ℝ) * w.radius := by
    have ht : |Real.sinc y - Real.sinc (w.q : ℝ)| ≤
        (w.firstAbs : ℝ) * |y - (w.q : ℝ)| := by
      simpa only [Real.norm_eq_abs] using htransport
    have hnonneg : (0 : ℝ) ≤ w.firstAbs := by
      simp only [Witness.firstAbs, Rat.cast_max, Rat.cast_abs]
      exact le_max_of_le_left (abs_nonneg _)
    exact ht.trans (mul_le_mul_of_nonneg_left hy hnonneg)
  have hcenterLo : (w.valueApprox : ℝ) - w.valueError ≤ Real.sinc w.q := by
    linarith [neg_abs_le (Real.sinc (w.q : ℝ) - w.valueApprox), hcenter]
  have hcenterHi : Real.sinc w.q ≤ (w.valueApprox : ℝ) + w.valueError := by
    linarith [le_abs_self (Real.sinc (w.q : ℝ) - w.valueApprox), hcenter]
  have hlo : (w.valueLower : ℝ) ≤ Real.sinc y := by
    have hcheck : (w.valueLower : ℝ) + w.firstAbs * w.radius ≤
        w.valueApprox - w.valueError := by exact_mod_cast hvl
    linarith [neg_abs_le (Real.sinc y - Real.sinc (w.q : ℝ)), hdiff]
  have hhi : Real.sinc y ≤ (w.valueUpper : ℝ) := by
    have hcheck : (w.valueApprox : ℝ) + w.valueError ≤
        w.valueUpper - w.firstAbs * w.radius := by exact_mod_cast hvu
    linarith [le_abs_self (Real.sinc y - Real.sinc (w.q : ℝ)), hdiff]
  exact ⟨⟨hlo, hhi⟩, hfirst, hsecond⟩

/-! ## Production reduced-argument regression -/

private def reducedQ : ℚ := 184814 / 625000

/-- The reduced argument occurring in twelve of the periodic `z±` rows of
production cell 4376.  This is the numerically delicate near-zero case. -/
def productionReducedWitness : Witness where
  q := reducedQ
  radius := 1 / 2500
  upper := 185064 / 625000
  sinApprox := reducedQ - reducedQ ^ 3 / 6 + reducedQ ^ 5 / 120 -
    reducedQ ^ 7 / 5040
  cosApprox := 1 - reducedQ ^ 2 / 2 + reducedQ ^ 4 / 24 -
    reducedQ ^ 6 / 720 + reducedQ ^ 8 / 40320
  trigError := 1 / 5000000
  valueLower := 98545 / 100000
  valueUpper := 985531 / 1000000
  firstLower := -97843 / 1000000
  firstUpper := -243935 / 2500000
  secondLower := -327341 / 1000000
  secondUpper := -40241 / 125000

theorem productionReducedWitness_checked : productionReducedWitness.check = true := by
  norm_num [productionReducedWitness, reducedQ, Witness.check,
    Witness.secondApprox, Witness.secondError, Witness.secondAbs,
    Witness.firstApprox, Witness.firstError, Witness.firstAbs,
    Witness.valueApprox, Witness.valueError]

private theorem productionReducedWitness_sin :
    |Real.sin (productionReducedWitness.q : ℝ) -
      (productionReducedWitness.sinApprox : ℝ)| ≤
        (productionReducedWitness.trigError : ℝ) := by
  have h := TranscendentalBounds.abs_sin_sub_sinTaylor7_le
    (upper := (1 : ℝ)) (x := (reducedQ : ℝ)) one_pos (by
      constructor <;> norm_num [reducedQ])
  simpa [productionReducedWitness, reducedQ,
    TranscendentalBounds.sinTaylor7] using
      h.trans (by norm_num [reducedQ])

private theorem productionReducedWitness_cos :
    |Real.cos (productionReducedWitness.q : ℝ) -
      (productionReducedWitness.cosApprox : ℝ)| ≤
        (productionReducedWitness.trigError : ℝ) := by
  have h := TranscendentalBounds.abs_cos_sub_cosTaylor8_le
    (upper := (1 : ℝ)) (x := (reducedQ : ℝ)) one_pos (by
      constructor <;> norm_num [reducedQ])
  simpa [productionReducedWitness, reducedQ,
    TranscendentalBounds.cosTaylor8] using
      h.trans (by norm_num [reducedQ])

/-- Fully kernel-checked jet enclosure on the delicate reduced argument cell. -/
theorem productionReducedWitness_sound {y : ℝ}
    (hy : |y - (184814 / 625000 : ℝ)| ≤ 1 / 2500) :
    ((98545 / 100000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 985531 / 1000000) ∧
    ((-97843 / 1000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -243935 / 2500000) ∧
    ((-327341 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -40241 / 125000) := by
  have hy' : |y - (productionReducedWitness.q : ℝ)| ≤
      (productionReducedWitness.radius : ℝ) := by
    simpa [productionReducedWitness, reducedQ] using hy
  simpa [productionReducedWitness, reducedQ] using
    productionReducedWitness.sound productionReducedWitness_checked
      productionReducedWitness_sin productionReducedWitness_cos hy'


end Zeta23Ext.SincJetCertificate

end
