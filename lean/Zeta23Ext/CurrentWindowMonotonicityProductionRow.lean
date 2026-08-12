/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowHybridRows
import Zeta23Ext.CurrentWindowArgumentReduction

/-!
# Executable production rows for current-window monotonicity

This module packages the range-reduction checks needed by generated hybrid
rows and checks one genuine second-derivative row end to end.
-/

noncomputable section

open Real
open scoped BigOperators

namespace Zeta23Ext.CurrentWindowMonotonicityProductionRow

open CurrentWindow
open CurrentWindowFiniteCertificate
open CurrentWindowHybridRows
open CurrentWindowArgumentReduction

/-- Executable validation of all fourteen finite obligations in a generated
second-derivative row: seven Taylor checks and seven range reductions. -/
def secondRowCheck (center : ℚ)
    (witness : Fin 7 → RationalTrigCell.Witness) : Bool :=
  decide (∀ j, RationalTrigCell.cosCheck (witness j) = true ∧
    reductionCheck j center (witness j) = true)

lemma secondRowCheck_sound {center : ℚ}
    {witness : Fin 7 → RationalTrigCell.Witness}
    (h : secondRowCheck center witness = true) :
    ∀ j, RationalTrigCell.cosCheck (witness j) = true ∧
      reductionCheck j center (witness j) = true := by
  simpa [secondRowCheck] using of_decide_eq_true h

/-- A generator-facing second-derivative row. Both the Taylor witness and
the argument range reduction are executable Boolean checks. -/
structure ReducedSecondRow (center radius : ℚ) where
  radius_nonneg : 0 ≤ radius
  witness : Fin 7 → RationalTrigCell.Witness
  checked : secondRowCheck center witness = true
  rationalArithmetic :
    (∑ j : Fin 7,
        -(coefficient j * frequency j ^ 2) *
          cosApproximation (witness j)) +
      (∑ j : Fin 7,
        |-(coefficient j * frequency j ^ 2)| * ((witness j).err : ℝ)) +
      153 * (radius : ℝ) ≤ 0

def ReducedSecondRow.cell {center radius : ℚ}
    (row : ReducedSecondRow center radius) : DerivativeCell where
  center := center
  radius := radius
  radius_nonneg := by exact_mod_cast row.radius_nonneg

def ReducedSecondRow.asCheckedSecondRow {center radius : ℚ}
    (row : ReducedSecondRow center radius) : CheckedSecondRow row.cell where
  witness := row.witness
  checked := fun j => (secondRowCheck_sound row.checked j).1
  reduced := fun j => reductionCheck_sound (secondRowCheck_sound row.checked j).2
  rationalArithmetic := row.rationalArithmetic

theorem ReducedSecondRow.secondUpper {center radius : ℚ}
    (row : ReducedSecondRow center radius) :
    deriv (deriv window) (center : ℝ) + jerkBound * (radius : ℝ) ≤ 0 := by
  simpa [ReducedSecondRow.cell] using row.asCheckedSecondRow.secondUpper

namespace RowOneSixteenth

def center : ℚ := 1 / 16
def radius : ℚ := 1 / 4096

def witness : Fin 7 → RationalTrigCell.Witness
  | ⟨0, _⟩ => ⟨0, 14145 / 160000, 1 / 32000, 3, 1 / 30000⟩
  | ⟨1, _⟩ => ⟨0, 3927 / 10000, 1 / 100000, 3, 1 / 90000⟩
  | ⟨2, _⟩ => ⟨0, 3927 / 5000, 1 / 100000, 3, 1 / 70000⟩
  | ⟨3, _⟩ => ⟨0, 11781 / 10000, 1 / 100000, 3, 1 / 8000⟩
  | ⟨4, _⟩ => ⟨0, 3927 / 2500, 1 / 100000, 3, 1 / 600⟩
  | ⟨5, _⟩ => ⟨0, 3927 / 2000, 1 / 100000, 3, 1 / 90⟩
  | ⟨6, _⟩ => ⟨0, 11781 / 5000, 1 / 100000, 3, 3 / 50⟩

theorem witnesses_checked (j : Fin 7) :
    RationalTrigCell.cosCheck (witness j) = true := by
  fin_cases j <;> norm_num [witness, RationalTrigCell.cosCheck]

theorem reductions_checked (j : Fin 7) :
    reductionCheck j center (witness j) = true := by
  fin_cases j <;>
    norm_num [reductionCheck, argumentInterval, center, witness,
      sqrtTwoInterval, piInterval, QInterval.smul, QInterval.sub,
      QInterval.add, QInterval.neg]

theorem row_checked : secondRowCheck center witness = true := by
  simp only [secondRowCheck, decide_eq_true_eq]
  intro j
  exact ⟨witnesses_checked j, reductions_checked j⟩

theorem arithmetic :
    (∑ j : Fin 7,
        -(coefficient j * frequency j ^ 2) *
          cosApproximation (witness j)) +
      (∑ j : Fin 7,
        |-(coefficient j * frequency j ^ 2)| * ((witness j).err : ℝ)) +
      153 * (radius : ℝ) ≤ 0 := by
  have hp := TranscendentalBounds.pi_rational_bounds
  have hp0 := Real.pi_pos
  have hp2lo :
      ((314159265358979323846 : ℝ) / 10 ^ 20) ^ 2 ≤ Real.pi ^ 2 := by
    nlinarith
  have hp2hi : Real.pi ^ 2 ≤
      ((314159265358979323847 : ℝ) / 10 ^ 20) ^ 2 := by
    nlinarith
  norm_num [coefficient, frequency, cosApproximation, witness, radius,
    TranscendentalBounds.cosTaylor8, Fin.sum_univ_succ, abs_mul, abs_pow,
    abs_of_pos hp0, Fin.succ] at ⊢
  nlinarith

def row : ReducedSecondRow center radius where
  radius_nonneg := by norm_num [radius]
  witness := witness
  checked := row_checked
  rationalArithmetic := arithmetic

/-- A real generated-style row, through Boolean trigonometric checks,
Boolean argument reduction, exact arithmetic, and the semantic derivative
bound consumed by the hybrid cover. -/
theorem production_row_secondUpper :
    deriv (deriv window) (1 / 16 : ℝ) + jerkBound * (1 / 4096 : ℝ) ≤ 0 := by
  simpa [center, radius] using row.secondUpper

end RowOneSixteenth

end Zeta23Ext.CurrentWindowMonotonicityProductionRow

end
