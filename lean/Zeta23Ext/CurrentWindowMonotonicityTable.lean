/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowMonotonicityArithmetic
import Zeta23Ext.CurrentFiniteReduction

/-! # Complete generated hybrid monotonicity table -/

noncomputable section

open Real Set
open scoped BigOperators

namespace Zeta23Ext.CurrentWindowMonotonicityTable

set_option maxHeartbeats 4000000

open CurrentWindow
open CurrentWindowArgumentReduction
open CurrentWindowHybridRows
open CurrentWindowMonotonicityArithmetic
open CurrentWindowMonotonicityProductionRow

def reductionIndex (j : Fin 7) (x : ℚ) : ℤ :=
  let q : ℚ := 2 * (j : ℕ) * x
  if 5 ≤ q then 5 else if 4 ≤ q then 4 else if 3 ≤ q then 3 else
    if 2 ≤ q then 2 else if 1 ≤ q then 1 else 0

def generatedCenter (j : Fin 7) (x : ℚ) : ℚ :=
  if (j : ℕ) = 0 then (2829 / 2000) * x
  else (2 * (j : ℕ) * x - reductionIndex j x) * (3927 / 1250)

def generatedRadius (j : Fin 7) (x : ℚ) : ℚ :=
  if (j : ℕ) = 0 then x / 2000 else 1 / 100000

def generatedCosWitness (j : Fin 7) (x : ℚ) : RationalTrigCell.Witness :=
  let c := generatedCenter j x
  let r := generatedRadius j x
  ⟨reductionIndex j x, c, r, 4, r + c ^ 9 / 40320⟩

def generatedSinWitness (j : Fin 7) (x : ℚ) : RationalTrigCell.Witness :=
  let c := generatedCenter j x
  let r := generatedRadius j x
  ⟨reductionIndex j x, c, r, 4, r + c ^ 8 / 5040⟩

def firstRowCheck (center : ℚ)
    (witness : Fin 7 → RationalTrigCell.Witness) : Bool :=
  decide (∀ j, RationalTrigCell.check (witness j) = true ∧
    reductionCheck j center (witness j) = true)

lemma firstRowCheck_sound {center : ℚ}
    {witness : Fin 7 → RationalTrigCell.Witness}
    (h : firstRowCheck center witness = true) :
    ∀ j, RationalTrigCell.check (witness j) = true ∧
      reductionCheck j center (witness j) = true := by
  simpa [firstRowCheck] using of_decide_eq_true h

structure ExecutableSecondRow (center radius : ℚ) where
  radius_nonneg : 0 ≤ radius
  witness : Fin 7 → RationalTrigCell.Witness
  checked : secondRowCheck center witness = true
  arithmeticChecked : secondArithmeticCheck radius witness = true

def ExecutableSecondRow.reduced {center radius : ℚ}
    (row : ExecutableSecondRow center radius) : ReducedSecondRow center radius where
  radius_nonneg := row.radius_nonneg
  witness := row.witness
  checked := row.checked
  rationalArithmetic := secondArithmeticCheck_sound row.arithmeticChecked

structure ExecutableFirstRow (center radius : ℚ) where
  radius_nonneg : 0 ≤ radius
  witness : Fin 7 → RationalTrigCell.Witness
  checked : firstRowCheck center witness = true
  arithmeticChecked : firstArithmeticCheck radius witness = true

def ExecutableFirstRow.cell {center radius : ℚ}
    (row : ExecutableFirstRow center radius) :
    CurrentWindowFiniteCertificate.DerivativeCell where
  center := center
  radius := radius
  radius_nonneg := by exact_mod_cast row.radius_nonneg

def ExecutableFirstRow.checkedRow {center radius : ℚ}
    (row : ExecutableFirstRow center radius) : CheckedFirstRow row.cell where
  witness := row.witness
  checked := fun j => (firstRowCheck_sound row.checked j).1
  reduced := fun j => reductionCheck_sound (firstRowCheck_sound row.checked j).2
  rationalArithmetic := firstArithmeticCheck_sound row.arithmeticChecked

def secondCenter (i : Fin 32) : ℚ := (2 * (i : ℕ) + 1) / 512
def secondRadius : ℚ := 1 / 512
def secondWitness (i : Fin 32) (j : Fin 7) : RationalTrigCell.Witness :=
  generatedCosWitness j (secondCenter i)

theorem second_checked (i : Fin 32) :
    secondRowCheck (secondCenter i) (secondWitness i) = true := by
  fin_cases i <;> simp only [secondRowCheck, decide_eq_true_eq] <;>
    intro j <;> fin_cases j <;>
    norm_num [secondRowCheck, secondWitness, generatedCosWitness,
      generatedCenter, generatedRadius, reductionIndex, secondCenter,
      RationalTrigCell.cosCheck, reductionCheck, argumentInterval,
      sqrtTwoInterval, piInterval, QInterval.smul, QInterval.sub,
      QInterval.add, QInterval.neg]

theorem second_arithmetic_checked (i : Fin 32) :
    secondArithmeticCheck secondRadius (secondWitness i) = true := by
  fin_cases i <;>
    norm_num [secondArithmeticCheck, secondScore, secondConstant,
      secondPiCoefficient, qCoefficient, periodicSquareFactor,
      qCosApproximation, qCosTaylor8, secondRadius, secondWitness,
      generatedCosWitness, generatedCenter, generatedRadius,
      reductionIndex, secondCenter, argumentInterval, sqrtTwoInterval,
      piInterval, QInterval.smul, QInterval.sub, QInterval.add,
      QInterval.neg, piSqLower, piSqUpper, Fin.sum_univ_succ, Fin.succ]

def secondExecutable (i : Fin 32) :
    ExecutableSecondRow (secondCenter i) secondRadius where
  radius_nonneg := by norm_num [secondRadius]
  witness := secondWitness i
  checked := second_checked i
  arithmeticChecked := second_arithmetic_checked i

def firstCenter : Fin 5 → ℚ
  | ⟨0, _⟩ => 7 / 50
  | ⟨1, _⟩ => 19 / 100
  | ⟨2, _⟩ => 11 / 40
  | ⟨3, _⟩ => 3 / 8
  | ⟨4, _⟩ => 37 / 80

def firstRadius : Fin 5 → ℚ
  | ⟨0, _⟩ => 3 / 200
  | ⟨1, _⟩ => 7 / 200
  | ⟨2, _⟩ => 1 / 20
  | ⟨3, _⟩ => 1 / 20
  | ⟨4, _⟩ => 3 / 80

def firstWitness (i : Fin 5) (j : Fin 7) : RationalTrigCell.Witness :=
  generatedSinWitness j (firstCenter i)

theorem first_checked (i : Fin 5) :
    firstRowCheck (firstCenter i) (firstWitness i) = true := by
  fin_cases i <;> simp only [firstRowCheck, decide_eq_true_eq] <;>
    intro j <;> fin_cases j <;>
    norm_num [firstRowCheck, firstWitness, generatedSinWitness,
      generatedCenter, generatedRadius, reductionIndex, firstCenter,
      RationalTrigCell.check, reductionCheck, argumentInterval,
      sqrtTwoInterval, piInterval, QInterval.smul, QInterval.sub,
      QInterval.add, QInterval.neg]

theorem first_arithmetic_checked (i : Fin 5) :
    firstArithmeticCheck (firstRadius i) (firstWitness i) = true := by
  fin_cases i <;>
    norm_num [firstArithmeticCheck, firstScore, firstSqrtCoefficient,
      firstPiCoefficient, qCoefficient, periodicFactor,
      qSinApproximation, qSinTaylor7, firstRadius, firstWitness,
      generatedSinWitness, generatedCenter, generatedRadius,
      reductionIndex, firstCenter, argumentInterval, sqrtTwoInterval,
      piInterval, QInterval.smul, QInterval.sub, QInterval.add,
      QInterval.neg, sqrtTwoLower, sqrtTwoUpper, Fin.sum_univ_succ, Fin.succ]

def firstExecutable (i : Fin 5) :
    ExecutableFirstRow (firstCenter i) (firstRadius i) where
  radius_nonneg := by fin_cases i <;> norm_num [firstRadius]
  witness := firstWitness i
  checked := first_checked i
  arithmeticChecked := first_arithmetic_checked i

def secondCell (i : Fin 32) :
    CurrentWindowFiniteCertificate.DerivativeCell :=
  (secondExecutable i).reduced.cell

def secondRow (i : Fin 32) : SecondRow (secondCell i) :=
  (secondExecutable i).reduced.asCheckedSecondRow.asSecondRow

def firstCell (i : Fin 5) :
    CurrentWindowFiniteCertificate.DerivativeCell :=
  (firstExecutable i).cell

def firstRow (i : Fin 5) : FirstRow (firstCell i) :=
  (firstExecutable i).checkedRow.asFirstRow

private lemma second_cell_covers (i : Fin 32) {s : ℝ}
    (hlo : ((i : ℕ) : ℝ) / 256 ≤ s)
    (hhi : s ≤ ((i : ℕ) + 1 : ℕ) / 256) :
    (secondCell i).Covers s := by
  unfold CurrentWindowFiniteCertificate.DerivativeCell.Covers
  rw [abs_le]
  change -((secondRadius : ℚ) : ℝ) ≤ s - (secondCenter i : ℚ) ∧
    s - (secondCenter i : ℚ) ≤ (secondRadius : ℚ)
  norm_num [secondRadius, secondCenter]
  norm_num only [Nat.cast_add, Nat.cast_one] at hhi
  constructor <;> linarith

theorem second_cover (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (1 / 8)) :
    ∃ i, (secondCell i).Covers s := by
  by_cases hend : s = 1 / 8
  · refine ⟨31, second_cell_covers 31 ?_ ?_⟩
    · rw [hend]
      norm_num
    · rw [hend]
      norm_num
  · have hslt : s < 1 / 8 := lt_of_le_of_ne hs.2 hend
    let n : ℕ := ⌊256 * s⌋₊
    have hnonneg : 0 ≤ 256 * s := mul_nonneg (by norm_num) hs.1
    have hn : n < 32 := by
      apply (Nat.floor_lt hnonneg).2
      norm_num
      nlinarith
    have hlo0 : (n : ℝ) ≤ 256 * s := Nat.floor_le hnonneg
    have hhi0 : 256 * s < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    refine ⟨⟨n, hn⟩, second_cell_covers ⟨n, hn⟩ ?_ ?_⟩
    · dsimp only
      nlinarith
    · dsimp only
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith

def firstLeft : Fin 5 → ℝ
  | ⟨0, _⟩ => 1 / 8
  | ⟨1, _⟩ => 31 / 200
  | ⟨2, _⟩ => 9 / 40
  | ⟨3, _⟩ => 13 / 40
  | ⟨4, _⟩ => 17 / 40

def firstRight : Fin 5 → ℝ
  | ⟨0, _⟩ => 31 / 200
  | ⟨1, _⟩ => 9 / 40
  | ⟨2, _⟩ => 13 / 40
  | ⟨3, _⟩ => 17 / 40
  | ⟨4, _⟩ => 1 / 2

private lemma first_cell_covers (i : Fin 5) {s : ℝ}
    (hlo : firstLeft i ≤ s) (hhi : s ≤ firstRight i) :
    (firstCell i).Covers s := by
  fin_cases i <;>
    unfold CurrentWindowFiniteCertificate.DerivativeCell.Covers <;>
    rw [abs_le] <;>
    change -((firstRadius _ : ℚ) : ℝ) ≤ s - (firstCenter _ : ℚ) ∧
      s - (firstCenter _ : ℚ) ≤ (firstRadius _ : ℚ) <;>
    norm_num [firstLeft, firstRight, firstCenter, firstRadius] at hlo hhi ⊢ <;>
    constructor <;> linarith

theorem first_cover (s : ℝ) (hs : s ∈ Icc (1 / 8 : ℝ) (1 / 2)) :
    ∃ i, (firstCell i).Covers s := by
  by_cases h0 : s ≤ 31 / 200
  · exact ⟨0, first_cell_covers 0 hs.1 h0⟩
  · by_cases h1 : s ≤ 9 / 40
    · exact ⟨1, first_cell_covers 1 (le_of_not_ge h0) h1⟩
    · by_cases h2 : s ≤ 13 / 40
      · exact ⟨2, first_cell_covers 2 (le_of_not_ge h1) h2⟩
      · by_cases h3 : s ≤ 17 / 40
        · exact ⟨3, first_cell_covers 3 (le_of_not_ge h2) h3⟩
        · exact ⟨4, first_cell_covers 4 (le_of_not_ge h3) hs.2⟩

def table : Table 32 5 where
  junction := 1 / 8
  junction_mem := by norm_num
  secondCells := secondCell
  secondRow := secondRow
  secondCover := second_cover
  firstCells := firstCell
  firstRow := firstRow
  firstCover := first_cover

theorem window_antitone : AntitoneOn window (Icc (0 : ℝ) (1 / 2)) :=
  table.window_antitone

def windowCertificate : CurrentWindow.WindowCertificate :=
  CurrentFiniteReduction.windowCertificate_of_antitone window_antitone

end Zeta23Ext.CurrentWindowMonotonicityTable

end
