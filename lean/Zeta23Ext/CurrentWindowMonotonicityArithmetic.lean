/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowMonotonicityProductionRow

/-! # Rational arithmetic checker for generated monotonicity rows -/

noncomputable section

open Real
open scoped BigOperators

namespace Zeta23Ext.CurrentWindowMonotonicityArithmetic

open CurrentWindow
open CurrentWindowHybridRows

def qCoefficient : Fin 7 → ℚ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3322500 / 1000000000
  | ⟨2, _⟩ => -7609135 / 1000000000
  | ⟨3, _⟩ => 1190194 / 1000000000
  | ⟨4, _⟩ => -731476 / 1000000000
  | ⟨5, _⟩ => -1680572 / 1000000000
  | ⟨6, _⟩ => 1141360 / 1000000000

def qCosTaylor8 (x : ℚ) : ℚ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320

def qCosApproximation (w : RationalTrigCell.Witness) : ℚ :=
  (-1 : ℚ) ^ w.k * qCosTaylor8 w.center

def periodicSquareFactor (k : Fin 6) : ℚ := 4 * ((k : ℕ) + 1) ^ 2

def secondConstant (radius : ℚ)
    (witness : Fin 7 → RationalTrigCell.Witness) : ℚ :=
  -(qCoefficient 0 * 2) * qCosApproximation (witness 0) +
    |-(qCoefficient 0 * 2)| * (witness 0).err + 153 * radius

def secondPiCoefficient
    (witness : Fin 7 → RationalTrigCell.Witness) : ℚ :=
  ∑ k : Fin 6, (
    -(qCoefficient k.succ * periodicSquareFactor k) *
        qCosApproximation (witness k.succ) +
      |-(qCoefficient k.succ * periodicSquareFactor k)| *
        (witness k.succ).err)

def piSqLower : ℚ :=
  (314159265358979323846 / 10 ^ 20) ^ 2

def piSqUpper : ℚ :=
  (314159265358979323847 / 10 ^ 20) ^ 2

def secondScore (radius : ℚ)
    (witness : Fin 7 → RationalTrigCell.Witness) : ℚ :=
  let b := secondPiCoefficient witness
  secondConstant radius witness + b * (if 0 ≤ b then piSqUpper else piSqLower)

def secondArithmeticCheck (radius : ℚ)
    (witness : Fin 7 → RationalTrigCell.Witness) : Bool :=
  decide (secondScore radius witness ≤ 0)

def qSinTaylor7 (x : ℚ) : ℚ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040

def qSinApproximation (w : RationalTrigCell.Witness) : ℚ :=
  (-1 : ℚ) ^ w.k * qSinTaylor7 w.center

def periodicFactor (k : Fin 6) : ℚ := 2 * ((k : ℕ) + 1)

def firstSqrtCoefficient
    (witness : Fin 7 → RationalTrigCell.Witness) : ℚ :=
  -qSinApproximation (witness 0) + (witness 0).err

def firstPiCoefficient
    (witness : Fin 7 → RationalTrigCell.Witness) : ℚ :=
  ∑ k : Fin 6, (
    -(qCoefficient k.succ * periodicFactor k) *
        qSinApproximation (witness k.succ) +
      |-(qCoefficient k.succ * periodicFactor k)| *
        (witness k.succ).err)

def sqrtTwoLower : ℚ := 707 / 500

def sqrtTwoUpper : ℚ := 283 / 200

def firstScore (radius : ℚ)
    (witness : Fin 7 → RationalTrigCell.Witness) : ℚ :=
  let a := firstSqrtCoefficient witness
  let b := firstPiCoefficient witness
  8 * radius + a * (if 0 ≤ a then sqrtTwoUpper else sqrtTwoLower) +
    b * (if 0 ≤ b then
      314159265358979323847 / 10 ^ 20
    else
      314159265358979323846 / 10 ^ 20)

def firstArithmeticCheck (radius : ℚ)
    (witness : Fin 7 → RationalTrigCell.Witness) : Bool :=
  decide (firstScore radius witness ≤ 0)

private lemma coefficient_cast (j : Fin 7) :
    (qCoefficient j : ℝ) = coefficient j := by
  fin_cases j <;> norm_num [qCoefficient, coefficient]

private lemma qCosApproximation_cast (w : RationalTrigCell.Witness) :
    (qCosApproximation w : ℝ) = cosApproximation w := by
  unfold qCosApproximation qCosTaylor8 cosApproximation
  norm_num [TranscendentalBounds.cosTaylor8]

private lemma qSinApproximation_cast (w : RationalTrigCell.Witness) :
    (qSinApproximation w : ℝ) = sinApproximation w := by
  unfold qSinApproximation qSinTaylor7 sinApproximation
  norm_num [TranscendentalBounds.sinTaylor7]

private lemma periodic_frequency_sq (k : Fin 6) :
    frequency k.succ ^ 2 = (periodicSquareFactor k : ℚ) * Real.pi ^ 2 := by
  fin_cases k <;> norm_num [frequency, periodicSquareFactor, Fin.succ] <;> ring

private lemma periodic_frequency (k : Fin 6) :
    frequency k.succ = (periodicFactor k : ℚ) * Real.pi := by
  fin_cases k <;> norm_num [frequency, periodicFactor, Fin.succ] <;> ring

private lemma second_expression_eq (radius : ℚ)
    (witness : Fin 7 → RationalTrigCell.Witness) :
    (∑ j : Fin 7,
        -(coefficient j * frequency j ^ 2) * cosApproximation (witness j)) +
      (∑ j : Fin 7,
        |-(coefficient j * frequency j ^ 2)| * ((witness j).err : ℝ)) +
      153 * (radius : ℝ) =
        (secondConstant radius witness : ℝ) +
          (secondPiCoefficient witness : ℝ) * Real.pi ^ 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp_rw [periodic_frequency_sq, ← coefficient_cast,
    ← qCosApproximation_cast]
  have hp2 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
  simp only [frequency, qCoefficient, Rat.cast_one, one_mul, neg_mul,
    abs_mul, abs_of_nonneg hp2]
  unfold secondConstant secondPiCoefficient
  norm_num [Fin.sum_univ_succ, periodicSquareFactor, Fin.succ,
    qCoefficient, abs_mul]
  ring

theorem secondArithmeticCheck_sound {radius : ℚ}
    {witness : Fin 7 → RationalTrigCell.Witness}
    (h : secondArithmeticCheck radius witness = true) :
    (∑ j : Fin 7,
        -(coefficient j * frequency j ^ 2) * cosApproximation (witness j)) +
      (∑ j : Fin 7,
        |-(coefficient j * frequency j ^ 2)| * ((witness j).err : ℝ)) +
      153 * (radius : ℝ) ≤ 0 := by
  rw [second_expression_eq]
  have hscore : secondScore radius witness ≤ 0 := by
    exact_mod_cast (show secondScore radius witness ≤ 0 by
      simpa [secondArithmeticCheck] using of_decide_eq_true h)
  have hp := TranscendentalBounds.pi_rational_bounds
  have hp0 := Real.pi_pos
  have hlo : (piSqLower : ℚ) ≤ Real.pi ^ 2 := by
    unfold piSqLower
    norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]
    nlinarith
  have hhi : Real.pi ^ 2 ≤ (piSqUpper : ℚ) := by
    unfold piSqUpper
    norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]
    nlinarith
  unfold secondScore at hscore
  dsimp only at hscore
  split_ifs at hscore with hb
  · have hbR : 0 ≤ (secondPiCoefficient witness : ℝ) := by exact_mod_cast hb
    have hmul := mul_le_mul_of_nonneg_left hhi hbR
    have hscoreR :
        (secondConstant radius witness : ℝ) +
          (secondPiCoefficient witness : ℝ) * (piSqUpper : ℝ) ≤ 0 := by
      exact_mod_cast hscore
    linarith
  · have hbR : (secondPiCoefficient witness : ℝ) ≤ 0 := by
      exact_mod_cast le_of_not_ge hb
    have hmul := mul_le_mul_of_nonpos_left hlo hbR
    have hscoreR :
        (secondConstant radius witness : ℝ) +
          (secondPiCoefficient witness : ℝ) * (piSqLower : ℝ) ≤ 0 := by
      exact_mod_cast hscore
    linarith

private lemma first_expression_eq (radius : ℚ)
    (witness : Fin 7 → RationalTrigCell.Witness) :
    (∑ j : Fin 7,
        -(coefficient j * frequency j) * sinApproximation (witness j)) +
      (∑ j : Fin 7,
        |-(coefficient j * frequency j)| * ((witness j).err : ℝ)) +
      8 * (radius : ℝ) =
        (firstSqrtCoefficient witness : ℝ) * Real.sqrt 2 +
          (firstPiCoefficient witness : ℝ) * Real.pi + 8 * (radius : ℝ) := by
  simp_rw [Fin.sum_univ_succ]
  simp_rw [periodic_frequency, ← coefficient_cast,
    ← qSinApproximation_cast]
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hp0 : 0 ≤ Real.pi := Real.pi_pos.le
  simp only [frequency, qCoefficient, Rat.cast_one, one_mul, neg_mul,
    abs_mul]
  unfold firstSqrtCoefficient firstPiCoefficient
  norm_num [Fin.sum_univ_succ, periodicFactor, Fin.succ,
    qCoefficient, abs_mul]
  simp only [abs_of_nonneg hs0, abs_of_nonneg hp0]
  ring

theorem firstArithmeticCheck_sound {radius : ℚ}
    {witness : Fin 7 → RationalTrigCell.Witness}
    (h : firstArithmeticCheck radius witness = true) :
    (∑ j : Fin 7,
        -(coefficient j * frequency j) * sinApproximation (witness j)) +
      (∑ j : Fin 7,
        |-(coefficient j * frequency j)| * ((witness j).err : ℝ)) +
      8 * (radius : ℝ) ≤ 0 := by
  rw [first_expression_eq]
  have hscore : firstScore radius witness ≤ 0 := by
    exact_mod_cast (show firstScore radius witness ≤ 0 by
      simpa [firstArithmeticCheck] using of_decide_eq_true h)
  have hs := TranscendentalBounds.sqrt_two_bounds
  have hp := TranscendentalBounds.pi_rational_bounds
  unfold firstScore at hscore
  dsimp only at hscore
  by_cases ha : 0 ≤ firstSqrtCoefficient witness
  · by_cases hb : 0 ≤ firstPiCoefficient witness
    · simp [ha, hb] at hscore
      have haR : 0 ≤ (firstSqrtCoefficient witness : ℝ) := by exact_mod_cast ha
      have hbR : 0 ≤ (firstPiCoefficient witness : ℝ) := by exact_mod_cast hb
      have hsa := mul_le_mul_of_nonneg_left hs.2 haR
      have hpb := mul_le_mul_of_nonneg_left hp.2.le hbR
      have hscoreR :
          8 * (radius : ℝ) + (firstSqrtCoefficient witness : ℝ) *
            (sqrtTwoUpper : ℝ) + (firstPiCoefficient witness : ℝ) *
            ((314159265358979323847 / 10 ^ 20 : ℚ) : ℝ) ≤ 0 := by
        exact_mod_cast hscore
      norm_num [sqrtTwoUpper] at hsa hscoreR
      linarith
    · simp [ha, hb] at hscore
      have haR : 0 ≤ (firstSqrtCoefficient witness : ℝ) := by exact_mod_cast ha
      have hbR : (firstPiCoefficient witness : ℝ) ≤ 0 := by
        exact_mod_cast le_of_not_ge hb
      have hsa := mul_le_mul_of_nonneg_left hs.2 haR
      have hpb := mul_le_mul_of_nonpos_left hp.1.le hbR
      have hscoreR :
          8 * (radius : ℝ) + (firstSqrtCoefficient witness : ℝ) *
            (sqrtTwoUpper : ℝ) + (firstPiCoefficient witness : ℝ) *
            ((314159265358979323846 / 10 ^ 20 : ℚ) : ℝ) ≤ 0 := by
        exact_mod_cast hscore
      norm_num [sqrtTwoUpper] at hsa hscoreR
      linarith
  · by_cases hb : 0 ≤ firstPiCoefficient witness
    · simp [ha, hb] at hscore
      have haR : (firstSqrtCoefficient witness : ℝ) ≤ 0 := by
        exact_mod_cast le_of_not_ge ha
      have hbR : 0 ≤ (firstPiCoefficient witness : ℝ) := by exact_mod_cast hb
      have hsa := mul_le_mul_of_nonpos_left hs.1 haR
      have hpb := mul_le_mul_of_nonneg_left hp.2.le hbR
      have hscoreR :
          8 * (radius : ℝ) + (firstSqrtCoefficient witness : ℝ) *
            (sqrtTwoLower : ℝ) + (firstPiCoefficient witness : ℝ) *
            ((314159265358979323847 / 10 ^ 20 : ℚ) : ℝ) ≤ 0 := by
        exact_mod_cast hscore
      norm_num [sqrtTwoLower] at hsa hscoreR
      linarith
    · simp [ha, hb] at hscore
      have haR : (firstSqrtCoefficient witness : ℝ) ≤ 0 := by
        exact_mod_cast le_of_not_ge ha
      have hbR : (firstPiCoefficient witness : ℝ) ≤ 0 := by
        exact_mod_cast le_of_not_ge hb
      have hsa := mul_le_mul_of_nonpos_left hs.1 haR
      have hpb := mul_le_mul_of_nonpos_left hp.1.le hbR
      have hscoreR :
          8 * (radius : ℝ) + (firstSqrtCoefficient witness : ℝ) *
            (sqrtTwoLower : ℝ) + (firstPiCoefficient witness : ℝ) *
            ((314159265358979323846 / 10 ^ 20 : ℚ) : ℝ) ≤ 0 := by
        exact_mod_cast hscore
      norm_num [sqrtTwoLower] at hsa hscoreR
      linarith

end Zeta23Ext.CurrentWindowMonotonicityArithmetic

end
