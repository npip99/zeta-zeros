/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowHybridMonotonicity
import Zeta23Ext.RationalTrigCell

/-!
# Semantic rows for hybrid current-window monotonicity

Rational cosine witnesses certify the second-derivative cells in the first
part of the interval.  The existing rational sine rows certify the
first-derivative cells in the second part.
-/

noncomputable section

open Real Set
open scoped BigOperators

namespace Zeta23Ext.CurrentWindowHybridRows

open CurrentWindow
open CurrentWindowAdmissibility
open CurrentWindowFiniteCertificate
open CurrentWindowHybridMonotonicity

def cosApproximation (w : RationalTrigCell.Witness) : ℝ :=
  ((-1 : ℝ) ^ w.k) *
    TranscendentalBounds.cosTaylor8 (w.center : ℝ)

def sinApproximation (w : RationalTrigCell.Witness) : ℝ :=
  ((-1 : ℝ) ^ w.k) *
    TranscendentalBounds.sinTaylor7 (w.center : ℝ)

/-- Seven semantic sine rows at an arbitrary first-derivative cell. -/
structure FirstRow (cell : DerivativeCell) where
  witness : Fin 7 → RationalTrigCell.Witness
  checked : ∀ j, RationalTrigCell.check (witness j) = true
  reduced : ∀ j,
    |(frequency j * cell.center - ((witness j).k : ℝ) * Real.pi) -
      ((witness j).center : ℝ)| ≤ ((witness j).radius : ℝ)
  arithmetic :
    (∑ j : Fin 7,
        -(coefficient j * frequency j) * sinApproximation (witness j)) +
      (∑ j : Fin 7,
        |-(coefficient j * frequency j)| * ((witness j).err : ℝ)) +
      curvatureBound * cell.radius ≤ 0

lemma FirstRow.sin_close {cell : DerivativeCell} (row : FirstRow cell)
    (j : Fin 7) :
    |Real.sin (frequency j * cell.center) -
      sinApproximation (row.witness j)| ≤ ((row.witness j).err : ℝ) := by
  have h := RationalTrigCell.sin_sound (row.checked j) (row.reduced j)
  unfold sinApproximation
  have hsign : |((-1 : ℝ) ^ (row.witness j).k)| = 1 := by
    rw [abs_zpow]
    norm_num
  calc
    |Real.sin (frequency j * cell.center) -
        ((-1 : ℝ) ^ (row.witness j).k) *
          TranscendentalBounds.sinTaylor7 ((row.witness j).center : ℝ)| =
      |((-1 : ℝ) ^ (row.witness j).k) *
        (((-1 : ℝ) ^ (row.witness j).k) *
            Real.sin (frequency j * cell.center) -
          TranscendentalBounds.sinTaylor7
            ((row.witness j).center : ℝ))| := by
        have hsquare : ((-1 : ℝ) ^ (row.witness j).k) ^ 2 = 1 := by
          nlinarith [sq_abs ((-1 : ℝ) ^ (row.witness j).k)]
        apply congrArg abs
        calc
          Real.sin (frequency j * cell.center) -
              (-1 : ℝ) ^ (row.witness j).k *
                TranscendentalBounds.sinTaylor7
                  ((row.witness j).center : ℝ) =
              (((-1 : ℝ) ^ (row.witness j).k) ^ 2) *
                Real.sin (frequency j * cell.center) -
              (-1 : ℝ) ^ (row.witness j).k *
                TranscendentalBounds.sinTaylor7
                  ((row.witness j).center : ℝ) := by rw [hsquare, one_mul]
          _ = _ := by ring
    _ = |((-1 : ℝ) ^ (row.witness j).k) *
          Real.sin (frequency j * cell.center) -
        TranscendentalBounds.sinTaylor7
          ((row.witness j).center : ℝ)| := by
      rw [abs_mul, hsign, one_mul]
    _ ≤ ((row.witness j).err : ℝ) := h

theorem FirstRow.firstUpper {cell : DerivativeCell}
    (row : FirstRow cell) :
    deriv window cell.center + curvatureBound * cell.radius ≤ 0 := by
  rw [deriv_window]
  have hsum := RationalTrigCell.weighted_sum_le
    (coefficient := fun j : Fin 7 => -(coefficient j * frequency j))
    (value := fun j => Real.sin (frequency j * cell.center))
    (approximation := fun j => sinApproximation (row.witness j))
    (error := fun j => ((row.witness j).err : ℝ))
    row.sin_close
  have hsum0 :
      (∑ j, -(coefficient j * frequency j *
        Real.sin (frequency j * cell.center))) ≤
        (∑ j, -(coefficient j * frequency j) *
          sinApproximation (row.witness j)) +
        ∑ j, |-(coefficient j * frequency j)| *
          ((row.witness j).err : ℝ) := by
    simpa only [neg_mul, mul_assoc] using hsum
  calc
    ∑ j, -(coefficient j * frequency j *
          Real.sin (frequency j * cell.center)) +
        curvatureBound * cell.radius ≤
      (∑ j, -(coefficient j * frequency j) *
          sinApproximation (row.witness j) +
        ∑ j, |-(coefficient j * frequency j)| *
          ((row.witness j).err : ℝ)) +
        curvatureBound * cell.radius := add_le_add_left hsum0 _
    _ ≤ 0 := row.arithmetic

/-- Producer-friendly first-derivative row.  Replacing the exact global
curvature envelope by the proved rational bound `8` leaves only rational
arithmetic and the finite trigonometric witnesses in generated data. -/
structure CheckedFirstRow (cell : DerivativeCell) where
  witness : Fin 7 → RationalTrigCell.Witness
  checked : ∀ j, RationalTrigCell.check (witness j) = true
  reduced : ∀ j,
    |(frequency j * cell.center - ((witness j).k : ℝ) * Real.pi) -
      ((witness j).center : ℝ)| ≤ ((witness j).radius : ℝ)
  rationalArithmetic :
    (∑ j : Fin 7,
        -(coefficient j * frequency j) * sinApproximation (witness j)) +
      (∑ j : Fin 7,
        |-(coefficient j * frequency j)| * ((witness j).err : ℝ)) +
      8 * cell.radius ≤ 0

def CheckedFirstRow.asFirstRow {cell : DerivativeCell}
    (row : CheckedFirstRow cell) : FirstRow cell where
  witness := row.witness
  checked := row.checked
  reduced := row.reduced
  arithmetic := by
    calc
      (∑ j : Fin 7,
          -(coefficient j * frequency j) * sinApproximation (row.witness j)) +
        (∑ j : Fin 7,
          |-(coefficient j * frequency j)| * ((row.witness j).err : ℝ)) +
        curvatureBound * cell.radius ≤
          (∑ j : Fin 7,
            -(coefficient j * frequency j) * sinApproximation (row.witness j)) +
          (∑ j : Fin 7,
            |-(coefficient j * frequency j)| * ((row.witness j).err : ℝ)) +
          8 * cell.radius := by
            gcongr
            exact cell.radius_nonneg
            exact curvatureBound_le_8
      _ ≤ 0 := row.rationalArithmetic

theorem CheckedFirstRow.firstUpper {cell : DerivativeCell}
    (row : CheckedFirstRow cell) :
    deriv window cell.center + curvatureBound * cell.radius ≤ 0 :=
  row.asFirstRow.firstUpper

/-- Seven semantic cosine rows at one second-derivative cell. -/
structure SecondRow (cell : DerivativeCell) where
  witness : Fin 7 → RationalTrigCell.Witness
  checked : ∀ j, RationalTrigCell.cosCheck (witness j) = true
  reduced : ∀ j,
    |(frequency j * cell.center - ((witness j).k : ℝ) * Real.pi) -
      ((witness j).center : ℝ)| ≤ ((witness j).radius : ℝ)
  arithmetic :
    (∑ j : Fin 7,
        -(coefficient j * frequency j ^ 2) *
          cosApproximation (witness j)) +
      (∑ j : Fin 7,
        |-(coefficient j * frequency j ^ 2)| *
          ((witness j).err : ℝ)) +
      jerkBound * cell.radius ≤ 0

lemma SecondRow.cos_close {cell : DerivativeCell} (row : SecondRow cell)
    (j : Fin 7) :
    |Real.cos (frequency j * cell.center) -
      cosApproximation (row.witness j)| ≤ ((row.witness j).err : ℝ) := by
  have h := RationalTrigCell.cos_sound (row.checked j) (row.reduced j)
  unfold cosApproximation
  have hsign : |((-1 : ℝ) ^ (row.witness j).k)| = 1 := by
    rw [abs_zpow]
    norm_num
  calc
    |Real.cos (frequency j * cell.center) -
        ((-1 : ℝ) ^ (row.witness j).k) *
          TranscendentalBounds.cosTaylor8 ((row.witness j).center : ℝ)| =
      |((-1 : ℝ) ^ (row.witness j).k) *
        (((-1 : ℝ) ^ (row.witness j).k) *
            Real.cos (frequency j * cell.center) -
          TranscendentalBounds.cosTaylor8
            ((row.witness j).center : ℝ))| := by
        have hsquare : ((-1 : ℝ) ^ (row.witness j).k) ^ 2 = 1 := by
          nlinarith [sq_abs ((-1 : ℝ) ^ (row.witness j).k)]
        apply congrArg abs
        calc
          Real.cos (frequency j * cell.center) -
              (-1 : ℝ) ^ (row.witness j).k *
                TranscendentalBounds.cosTaylor8
                  ((row.witness j).center : ℝ) =
              (((-1 : ℝ) ^ (row.witness j).k) ^ 2) *
                Real.cos (frequency j * cell.center) -
              (-1 : ℝ) ^ (row.witness j).k *
                TranscendentalBounds.cosTaylor8
                  ((row.witness j).center : ℝ) := by rw [hsquare, one_mul]
          _ = _ := by ring
    _ = |((-1 : ℝ) ^ (row.witness j).k) *
          Real.cos (frequency j * cell.center) -
        TranscendentalBounds.cosTaylor8
          ((row.witness j).center : ℝ)| := by
      rw [abs_mul, hsign, one_mul]
    _ ≤ ((row.witness j).err : ℝ) := h

theorem SecondRow.secondUpper {cell : DerivativeCell}
    (row : SecondRow cell) :
    deriv (deriv window) cell.center + jerkBound * cell.radius ≤ 0 := by
  rw [deriv2_window]
  have hsum := RationalTrigCell.weighted_sum_le
    (coefficient := fun j : Fin 7 => -(coefficient j * frequency j ^ 2))
    (value := fun j => Real.cos (frequency j * cell.center))
    (approximation := fun j => cosApproximation (row.witness j))
    (error := fun j => ((row.witness j).err : ℝ))
    row.cos_close
  have hsum0 :
      (∑ j, -(coefficient j * frequency j ^ 2 *
        Real.cos (frequency j * cell.center))) ≤
        (∑ j, -(coefficient j * frequency j ^ 2) *
          cosApproximation (row.witness j)) +
        ∑ j, |-(coefficient j * frequency j ^ 2)| *
          ((row.witness j).err : ℝ) := by
    simpa only [neg_mul, mul_assoc] using hsum
  calc
    ∑ j, -(coefficient j * frequency j ^ 2 *
          Real.cos (frequency j * cell.center)) +
        jerkBound * cell.radius ≤
      (∑ j, -(coefficient j * frequency j ^ 2) *
          cosApproximation (row.witness j) +
        ∑ j, |-(coefficient j * frequency j ^ 2)| *
          ((row.witness j).err : ℝ)) +
        jerkBound * cell.radius := add_le_add_left hsum0 _
    _ ≤ 0 := row.arithmetic

/-- Producer-friendly second-derivative row using the rational global jerk
envelope `153`. -/
structure CheckedSecondRow (cell : DerivativeCell) where
  witness : Fin 7 → RationalTrigCell.Witness
  checked : ∀ j, RationalTrigCell.cosCheck (witness j) = true
  reduced : ∀ j,
    |(frequency j * cell.center - ((witness j).k : ℝ) * Real.pi) -
      ((witness j).center : ℝ)| ≤ ((witness j).radius : ℝ)
  rationalArithmetic :
    (∑ j : Fin 7,
        -(coefficient j * frequency j ^ 2) *
          cosApproximation (witness j)) +
      (∑ j : Fin 7,
        |-(coefficient j * frequency j ^ 2)| *
          ((witness j).err : ℝ)) +
      153 * cell.radius ≤ 0

def CheckedSecondRow.asSecondRow {cell : DerivativeCell}
    (row : CheckedSecondRow cell) : SecondRow cell where
  witness := row.witness
  checked := row.checked
  reduced := row.reduced
  arithmetic := by
    calc
      (∑ j : Fin 7,
          -(coefficient j * frequency j ^ 2) *
            cosApproximation (row.witness j)) +
        (∑ j : Fin 7,
          |-(coefficient j * frequency j ^ 2)| *
            ((row.witness j).err : ℝ)) +
        jerkBound * cell.radius ≤
          (∑ j : Fin 7,
            -(coefficient j * frequency j ^ 2) *
              cosApproximation (row.witness j)) +
          (∑ j : Fin 7,
            |-(coefficient j * frequency j ^ 2)| *
              ((row.witness j).err : ℝ)) +
          153 * cell.radius := by
            gcongr
            exact cell.radius_nonneg
            exact jerkBound_le_153
      _ ≤ 0 := row.rationalArithmetic

theorem CheckedSecondRow.secondUpper {cell : DerivativeCell}
    (row : CheckedSecondRow cell) :
    deriv (deriv window) cell.center + jerkBound * cell.radius ≤ 0 :=
  row.asSecondRow.secondUpper

/-- A completely semantic hybrid certificate.  Only rational trigonometric
rows and the finite geometric covers are producer data. -/
structure Table (nSecond nFirst : ℕ) where
  junction : ℝ
  junction_mem : junction ∈ Icc (0 : ℝ) (1 / 2)
  secondCells : Fin nSecond → DerivativeCell
  secondRow : ∀ i, SecondRow (secondCells i)
  secondCover : ∀ s ∈ Icc (0 : ℝ) junction,
    ∃ i, (secondCells i).Covers s
  firstCells : Fin nFirst → DerivativeCell
  firstRow : ∀ i, FirstRow (firstCells i)
  firstCover : ∀ s ∈ Icc junction (1 / 2),
    ∃ i, (firstCells i).Covers s

def Table.toCertificate {nSecond nFirst : ℕ}
    (table : Table nSecond nFirst) :
    CurrentWindowHybridMonotonicity.Certificate nSecond nFirst where
  junction := table.junction
  junction_mem := table.junction_mem
  secondCells := table.secondCells
  secondUpper := fun i => (table.secondRow i).secondUpper
  secondCover := table.secondCover
  firstCells := table.firstCells
  firstUpper := fun i => (table.firstRow i).firstUpper
  firstCover := table.firstCover

theorem Table.window_antitone {nSecond nFirst : ℕ}
    (table : Table nSecond nFirst) :
    AntitoneOn window (Icc (0 : ℝ) (1 / 2)) :=
  CurrentWindowHybridMonotonicity.window_antitone table.toCertificate

end Zeta23Ext.CurrentWindowHybridRows
