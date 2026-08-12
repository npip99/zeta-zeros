/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowUniformGrid
import Zeta23Ext.RationalTrigCell

/-!
# Semantic rows for the current-window monotonicity grid

Each generated centre row contains seven rational sine range-reduction
witnesses.  Their Boolean checks and exact reduction proofs imply the real
derivative bound used by `CurrentWindowUniformGrid.Certificate`.
-/

noncomputable section

open Real Set
open scoped BigOperators

namespace Zeta23Ext.CurrentWindowMonotonicityRows

open CurrentWindow
open CurrentWindowAdmissibility
open CurrentWindowUniformGrid

/-- The signed Taylor approximation corresponding to a range-reduced row. -/
def approximation (w : RationalTrigCell.Witness) : ℝ :=
  ((-1 : ℝ) ^ w.k) *
    TranscendentalBounds.sinTaylor7 (w.center : ℝ)

/-- Seven proof-producing sine rows at one derivative-cell centre. -/
structure CenterRow (n : ℕ) (i : Fin n) where
  witness : Fin 7 → RationalTrigCell.Witness
  checked : ∀ j, RationalTrigCell.check (witness j) = true
  reduced : ∀ j,
    |(frequency j * (cell n i).center -
        ((witness j).k : ℝ) * Real.pi) -
      ((witness j).center : ℝ)| ≤ ((witness j).radius : ℝ)
  arithmetic :
    (∑ j : Fin 7,
        -(coefficient j * frequency j) * approximation (witness j)) +
      (∑ j : Fin 7,
        |-(coefficient j * frequency j)| * ((witness j).err : ℝ)) +
      curvatureBound * (cell n i).radius ≤ 0

lemma CenterRow.sin_close {n : ℕ} {i : Fin n} (row : CenterRow n i)
    (j : Fin 7) :
    |Real.sin (frequency j * (cell n i).center) -
      approximation (row.witness j)| ≤ ((row.witness j).err : ℝ) := by
  have h := RationalTrigCell.sin_sound (row.checked j) (row.reduced j)
  unfold approximation
  have hsign : |((-1 : ℝ) ^ (row.witness j).k)| = 1 := by
    rw [abs_zpow]
    norm_num
  calc
    |Real.sin (frequency j * (cell n i).center) -
        ((-1 : ℝ) ^ (row.witness j).k) *
          TranscendentalBounds.sinTaylor7 ((row.witness j).center : ℝ)| =
      |((-1 : ℝ) ^ (row.witness j).k) *
        (((-1 : ℝ) ^ (row.witness j).k) *
            Real.sin (frequency j * (cell n i).center) -
          TranscendentalBounds.sinTaylor7
            ((row.witness j).center : ℝ))| := by
        have hsquare : ((-1 : ℝ) ^ (row.witness j).k) ^ 2 = 1 := by
          rw [zpow_two]
          norm_num
        apply congrArg abs
        nlinarith
    _ = |((-1 : ℝ) ^ (row.witness j).k) *
          Real.sin (frequency j * (cell n i).center) -
        TranscendentalBounds.sinTaylor7
          ((row.witness j).center : ℝ)| := by
      rw [abs_mul, hsign, one_mul]
    _ ≤ ((row.witness j).err : ℝ) := h

theorem CenterRow.centerUpper {n : ℕ} {i : Fin n}
    (row : CenterRow n i) :
    deriv window (cell n i).center +
      curvatureBound * (cell n i).radius ≤ 0 := by
  rw [deriv_window]
  have hsum := RationalTrigCell.weighted_sum_le
    (coefficient := fun j : Fin 7 => -(coefficient j * frequency j))
    (value := fun j => Real.sin (frequency j * (cell n i).center))
    (approximation := fun j => approximation (row.witness j))
    (error := fun j => ((row.witness j).err : ℝ))
    row.sin_close
  linarith [row.arithmetic]

/-- A generated family of semantic centre rows produces exactly the compact
uniform-grid certificate consumed by the global monotonicity proof. -/
structure Table (n : ℕ) where
  n_pos : 0 < n
  row : ∀ i : Fin n, CenterRow n i

def Table.toUniformCertificate {n : ℕ} (table : Table n) :
    CurrentWindowUniformGrid.Certificate n where
  n_pos := table.n_pos
  centerUpper := fun i => (table.row i).centerUpper

theorem Table.window_antitone {n : ℕ} (table : Table n) :
    AntitoneOn window (Icc (0 : ℝ) (1 / 2)) :=
  table.toUniformCertificate.window_antitone

end Zeta23Ext.CurrentWindowMonotonicityRows

