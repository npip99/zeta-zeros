/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.SincJetCertificate
import Zeta23Ext.CurrentWindowArgumentReduction
import Zeta23Ext.CurrentKernelTotalDerivatives

/-!
# Fully executable sinc-jet rows

`SincJetCertificate.Witness` has the useful analytic semantics, but its sine
and cosine estimates were formerly separate theorem arguments.  This module
packages the range reduction, Taylor estimates, and jet arithmetic into one
Boolean-checkable record.  Generated kernel tables can therefore contain
data only: no row-specific Lean proof terms are required.
-/

noncomputable section

open Real

namespace Zeta23Ext.CheckedSincJet

open SincJetCertificate
open CurrentWindowArgumentReduction

/-- Rational versions of the two Taylor polynomials. -/
def sinTaylor7Q (x : ℚ) : ℚ := x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040
def cosTaylor8Q (x : ℚ) : ℚ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320

/-- The parity sign introduced by reduction modulo an integral multiple of
`pi`.  Keeping this rational makes every generated check decidable. -/
def paritySign (k : ℤ) : ℚ := if Even k then 1 else -1

lemma paritySign_cast (k : ℤ) :
    (paritySign k : ℝ) = (-1 : ℝ) ^ k := by
  rw [paritySign, neg_one_zpow_eq_ite]
  split_ifs <;> norm_num

/-- Exact enclosure of the reduced rational jet centre `q - k*pi`. -/
def reducedCenterInterval (q : ℚ) (k : ℤ) : QInterval :=
  (⟨q, q⟩ : QInterval).sub (piInterval.smul (k : ℚ))

lemma reducedCenter_mem (q : ℚ) (k : ℤ) :
    (reducedCenterInterval q k).Mem ((q : ℝ) - (k : ℝ) * Real.pi) := by
  exact QInterval.mem_sub ⟨le_rfl, le_rfl⟩
    (QInterval.mem_smul pi_mem (k : ℚ))

/-- One completely checked positive sinc-jet row. -/
structure Witness where
  jet : SincJetCertificate.Witness
  trig : RationalTrigCell.Witness

def Witness.check (w : Witness) : Bool :=
  w.jet.check && RationalTrigCell.check w.trig &&
    RationalTrigCell.cosCheck w.trig &&
    decide (w.jet.sinApprox = paritySign w.trig.k * sinTaylor7Q w.trig.center ∧
      w.jet.cosApprox = paritySign w.trig.k * cosTaylor8Q w.trig.center ∧
      w.trig.err ≤ w.jet.trigError ∧
      w.trig.center - w.trig.radius ≤
        (reducedCenterInterval w.jet.q w.trig.k).lo ∧
      (reducedCenterInterval w.jet.q w.trig.k).hi ≤
        w.trig.center + w.trig.radius)

private lemma check_facts {w : Witness} (h : w.check = true) :
    w.jet.check = true ∧ RationalTrigCell.check w.trig = true ∧
      RationalTrigCell.cosCheck w.trig = true ∧
      w.jet.sinApprox = paritySign w.trig.k * sinTaylor7Q w.trig.center ∧
      w.jet.cosApprox = paritySign w.trig.k * cosTaylor8Q w.trig.center ∧
      w.trig.err ≤ w.jet.trigError ∧
      w.trig.center - w.trig.radius ≤
        (reducedCenterInterval w.jet.q w.trig.k).lo ∧
      (reducedCenterInterval w.jet.q w.trig.k).hi ≤
        w.trig.center + w.trig.radius := by
  simp only [Witness.check, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, of_decide_eq_true h.2⟩

private lemma jet_positive_facts {w : Witness} (h : w.check = true) :
    0 < w.jet.q - w.jet.radius := by
  have hj := (check_facts h).1
  rw [SincJetCertificate.Witness.check] at hj
  exact (of_decide_eq_true hj).1

/-- Checked quotient rows are deliberately separated from the removable
point.  The handful of production cells meeting a zero argument need the
separate total-series row, rather than silently applying quotient formulas. -/
theorem Witness.argument_ne_zero {w : Witness} (h : w.check = true) {y : ℝ}
    (hy : |y - (w.jet.q : ℝ)| ≤ (w.jet.radius : ℝ)) : y ≠ 0 := by
  have hp : (0 : ℝ) < (w.jet.q : ℝ) - w.jet.radius := by
    exact_mod_cast jet_positive_facts h
  rw [abs_le] at hy
  intro hy0
  subst y
  linarith [hy.1]

private lemma reduction_sound {w : Witness} (h : w.check = true) :
    |(((w.jet.q : ℝ) - (w.trig.k : ℝ) * Real.pi) -
      (w.trig.center : ℝ))| ≤ (w.trig.radius : ℝ) := by
  have hf := check_facts h
  have hm := reducedCenter_mem w.jet.q w.trig.k
  have hloCast : (w.trig.center : ℝ) - w.trig.radius ≤
      ((reducedCenterInterval w.jet.q w.trig.k).lo : ℝ) := by
    exact_mod_cast hf.2.2.2.2.2.2.1
  have hhiCast : ((reducedCenterInterval w.jet.q w.trig.k).hi : ℝ) ≤
      (w.trig.center : ℝ) + w.trig.radius := by
    exact_mod_cast hf.2.2.2.2.2.2.2
  have hlo : (w.trig.center : ℝ) - w.trig.radius ≤
      (w.jet.q : ℝ) - (w.trig.k : ℝ) * Real.pi := by
    exact hloCast.trans hm.1
  have hhi : (w.jet.q : ℝ) - (w.trig.k : ℝ) * Real.pi ≤
      (w.trig.center : ℝ) + w.trig.radius := by
    exact hm.2.trans hhiCast
  rw [abs_le]
  constructor <;> linarith

private lemma sin_close {w : Witness} (h : w.check = true) :
    |Real.sin (w.jet.q : ℝ) - (w.jet.sinApprox : ℝ)| ≤
      (w.jet.trigError : ℝ) := by
  have hf := check_facts h
  have hs := RationalTrigCell.sin_sound hf.2.1
    (reduction_sound h)
  have hsign : ((paritySign w.trig.k : ℚ) : ℝ) =
      (-1 : ℝ) ^ w.trig.k := paritySign_cast _
  have hsq : ((-1 : ℝ) ^ w.trig.k) ^ 2 = 1 := by
    rw [neg_one_zpow_eq_ite]
    split_ifs <;> norm_num
  have hpoly : ((sinTaylor7Q w.trig.center : ℚ) : ℝ) =
      TranscendentalBounds.sinTaylor7 (w.trig.center : ℝ) := by
    simp [sinTaylor7Q, TranscendentalBounds.sinTaylor7]
  have happ : (w.jet.sinApprox : ℝ) =
      ((-1 : ℝ) ^ w.trig.k) *
        TranscendentalBounds.sinTaylor7 (w.trig.center : ℝ) := by
    rw [hf.2.2.2.1, Rat.cast_mul, hsign, hpoly]
  rw [happ, show Real.sin (w.jet.q : ℝ) -
      (-1 : ℝ) ^ w.trig.k *
        TranscendentalBounds.sinTaylor7 (w.trig.center : ℝ) =
      ((-1 : ℝ) ^ w.trig.k) *
        (((-1 : ℝ) ^ w.trig.k * Real.sin (w.jet.q : ℝ)) -
          TranscendentalBounds.sinTaylor7 (w.trig.center : ℝ)) by
      calc
        Real.sin (w.jet.q : ℝ) -
            (-1 : ℝ) ^ w.trig.k *
              TranscendentalBounds.sinTaylor7 (w.trig.center : ℝ) =
            (((-1 : ℝ) ^ w.trig.k) ^ 2) * Real.sin (w.jet.q : ℝ) -
              (-1 : ℝ) ^ w.trig.k *
                TranscendentalBounds.sinTaylor7 (w.trig.center : ℝ) := by
                  rw [hsq, one_mul]
        _ = _ := by ring]
  rw [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  exact hs.trans (by exact_mod_cast hf.2.2.2.2.2.1)

private lemma cos_close {w : Witness} (h : w.check = true) :
    |Real.cos (w.jet.q : ℝ) - (w.jet.cosApprox : ℝ)| ≤
      (w.jet.trigError : ℝ) := by
  have hf := check_facts h
  have hc := RationalTrigCell.cos_sound hf.2.2.1
    (reduction_sound h)
  have hsign : ((paritySign w.trig.k : ℚ) : ℝ) =
      (-1 : ℝ) ^ w.trig.k := paritySign_cast _
  have hsq : ((-1 : ℝ) ^ w.trig.k) ^ 2 = 1 := by
    rw [neg_one_zpow_eq_ite]
    split_ifs <;> norm_num
  have hpoly : ((cosTaylor8Q w.trig.center : ℚ) : ℝ) =
      TranscendentalBounds.cosTaylor8 (w.trig.center : ℝ) := by
    simp [cosTaylor8Q, TranscendentalBounds.cosTaylor8]
  have happ : (w.jet.cosApprox : ℝ) =
      ((-1 : ℝ) ^ w.trig.k) *
        TranscendentalBounds.cosTaylor8 (w.trig.center : ℝ) := by
    rw [hf.2.2.2.2.1, Rat.cast_mul, hsign, hpoly]
  rw [happ, show Real.cos (w.jet.q : ℝ) -
      (-1 : ℝ) ^ w.trig.k *
        TranscendentalBounds.cosTaylor8 (w.trig.center : ℝ) =
      ((-1 : ℝ) ^ w.trig.k) *
        (((-1 : ℝ) ^ w.trig.k * Real.cos (w.jet.q : ℝ)) -
          TranscendentalBounds.cosTaylor8 (w.trig.center : ℝ)) by
      calc
        Real.cos (w.jet.q : ℝ) -
            (-1 : ℝ) ^ w.trig.k *
              TranscendentalBounds.cosTaylor8 (w.trig.center : ℝ) =
            (((-1 : ℝ) ^ w.trig.k) ^ 2) * Real.cos (w.jet.q : ℝ) -
              (-1 : ℝ) ^ w.trig.k *
                TranscendentalBounds.cosTaylor8 (w.trig.center : ℝ) := by
                  rw [hsq, one_mul]
        _ = _ := by ring]
  rw [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  exact hc.trans (by exact_mod_cast hf.2.2.2.2.2.1)

/-- A successful Boolean row check discharges every analytic premise of the
layered sinc-jet theorem. -/
theorem Witness.sound {w : Witness} (h : w.check = true) {y : ℝ}
    (hy : |y - (w.jet.q : ℝ)| ≤ (w.jet.radius : ℝ)) :
    ((w.jet.valueLower : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ w.jet.valueUpper) ∧
    ((w.jet.firstLower : ℝ) ≤ CurrentKernelTotalDerivatives.sincD1Total y ∧
      CurrentKernelTotalDerivatives.sincD1Total y ≤ w.jet.firstUpper) ∧
    ((w.jet.secondLower : ℝ) ≤ CurrentKernelTotalDerivatives.sincD2Total y ∧
      CurrentKernelTotalDerivatives.sincD2Total y ≤ w.jet.secondUpper) := by
  have hn := w.argument_ne_zero h hy
  simpa [CurrentKernelTotalDerivatives.sincD1Total_eq hn,
    CurrentKernelTotalDerivatives.sincD2Total_eq hn] using
      w.jet.sound (check_facts h).1 (sin_close h) (cos_close h) hy

/-! ## Reflected rows

The current kernel has many negative `minusArgument`s.  Reflection is encoded
as data as well, so the generator does not emit per-row parity proofs.
-/

structure SignedWitness where
  positive : Witness
  reflected : Bool

def SignedWitness.check (w : SignedWitness) : Bool := w.positive.check

def SignedWitness.center (w : SignedWitness) : ℚ :=
  if w.reflected then -w.positive.jet.q else w.positive.jet.q

def SignedWitness.valueLower (w : SignedWitness) : ℚ :=
  w.positive.jet.valueLower
def SignedWitness.valueUpper (w : SignedWitness) : ℚ :=
  w.positive.jet.valueUpper
def SignedWitness.firstLower (w : SignedWitness) : ℚ :=
  if w.reflected then -w.positive.jet.firstUpper else w.positive.jet.firstLower
def SignedWitness.firstUpper (w : SignedWitness) : ℚ :=
  if w.reflected then -w.positive.jet.firstLower else w.positive.jet.firstUpper
def SignedWitness.secondLower (w : SignedWitness) : ℚ :=
  w.positive.jet.secondLower
def SignedWitness.secondUpper (w : SignedWitness) : ℚ :=
  w.positive.jet.secondUpper

private lemma sincD1Total_neg (x : ℝ) :
    CurrentKernelTotalDerivatives.sincD1Total (-x) =
      -CurrentKernelTotalDerivatives.sincD1Total x := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [CurrentKernelTotalDerivatives.sincD1Total_eq (neg_ne_zero.mpr hx),
      CurrentKernelTotalDerivatives.sincD1Total_eq hx]
    unfold SincDerivativeCertificate.sincD1
    rw [Real.cos_neg, Real.sin_neg]
    ring

private lemma sincD2Total_neg (x : ℝ) :
    CurrentKernelTotalDerivatives.sincD2Total (-x) =
      CurrentKernelTotalDerivatives.sincD2Total x := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [CurrentKernelTotalDerivatives.sincD2Total_eq (neg_ne_zero.mpr hx),
      CurrentKernelTotalDerivatives.sincD2Total_eq hx]
    unfold SincDerivativeCertificate.sincD2
      SincDerivativeCertificate.secondNumerator
    rw [Real.cos_neg, Real.sin_neg]
    ring

/-- Executable positive/reflected jet semantics, stated directly for the
all-point derivative functions used by the current weight. -/
theorem SignedWitness.sound {w : SignedWitness} (h : w.check = true) {y : ℝ}
    (hy : |y - (w.center : ℝ)| ≤ (w.positive.jet.radius : ℝ)) :
    ((w.valueLower : ℝ) ≤ Real.sinc y ∧ Real.sinc y ≤ w.valueUpper) ∧
    ((w.firstLower : ℝ) ≤ CurrentKernelTotalDerivatives.sincD1Total y ∧
      CurrentKernelTotalDerivatives.sincD1Total y ≤ w.firstUpper) ∧
    ((w.secondLower : ℝ) ≤ CurrentKernelTotalDerivatives.sincD2Total y ∧
      CurrentKernelTotalDerivatives.sincD2Total y ≤ w.secondUpper) := by
  cases hr : w.reflected
  · have hp : w.positive.check = true := by
      simpa [SignedWitness.check] using h
    have hy' : |y - (w.positive.jet.q : ℝ)| ≤
        (w.positive.jet.radius : ℝ) := by
      simpa [SignedWitness.center, hr] using hy
    simpa [SignedWitness.check, SignedWitness.center, SignedWitness.valueLower,
      SignedWitness.valueUpper, SignedWitness.firstLower, SignedWitness.firstUpper,
      SignedWitness.secondLower, SignedWitness.secondUpper, hr] using
        w.positive.sound hp hy'
  · have hy' : |-y - (w.positive.jet.q : ℝ)| ≤
        (w.positive.jet.radius : ℝ) := by
      rw [show -y - (w.positive.jet.q : ℝ) =
        -(y + (w.positive.jet.q : ℝ)) by ring, abs_neg]
      simpa [SignedWitness.center, hr] using hy
    have hp : w.positive.check = true := by
      simpa [SignedWitness.check] using h
    have hs := w.positive.sound hp hy'
    rw [Real.sinc_neg, sincD1Total_neg, sincD2Total_neg] at hs
    simpa [SignedWitness.valueLower, SignedWitness.valueUpper,
      SignedWitness.firstLower, SignedWitness.firstUpper,
      SignedWitness.secondLower, SignedWitness.secondUpper, hr] using
        ⟨hs.1, ⟨by linarith [hs.2.1.2], by linarith [hs.2.1.1]⟩, hs.2.2⟩

/-! A data-only regression using the delicate production reduced argument. -/

def regressionJet : SincJetCertificate.Witness where
  q := 184814 / 625000
  radius := 1 / 2500
  upper := 185064 / 625000
  sinApprox := sinTaylor7Q (184814 / 625000)
  cosApprox := cosTaylor8Q (184814 / 625000)
  trigError := 1 / 5000000
  valueLower := 98545 / 100000
  valueUpper := 985531 / 1000000
  firstLower := -97843 / 1000000
  firstUpper := -243935 / 2500000
  secondLower := -327341 / 1000000
  secondUpper := -40241 / 125000

def regression : Witness where
  jet := regressionJet
  trig := ⟨0, 184814 / 625000, 0, 1, 1 / 5000000⟩

example : regression.check = true := by
  norm_num [Witness.check, regression, regressionJet,
    RationalTrigCell.check, RationalTrigCell.cosCheck, paritySign,
    sinTaylor7Q, cosTaylor8Q, reducedCenterInterval, QInterval.sub,
    QInterval.add, QInterval.neg, QInterval.smul, piInterval,
    SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

end Zeta23Ext.CheckedSincJet
end
