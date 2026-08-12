/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowFiniteCertificate

/-!
# Uniform-grid monotonicity certificates

The analytic monotonicity theorem only needs finitely many upper bounds for
`v'` at cell centres.  This module discharges the geometric coverage of the
standard uniform grid once and for all, so generated certificate data does not
carry thousands of repetitive real-domain coverage proofs.
-/

noncomputable section

open Real Set

namespace Zeta23Ext.CurrentWindowUniformGrid

open CurrentWindowAdmissibility
open CurrentWindowFiniteCertificate

def leftEndpoint : ℝ := 1 / 4096
def rightEndpoint : ℝ := 1 / 2

def step (n : ℕ) : ℝ := (rightEndpoint - leftEndpoint) / n

def cell (n : ℕ) (i : Fin n) : DerivativeCell where
  center := leftEndpoint + ((i : ℕ) + (1 : ℝ) / 2) * step n
  radius := step n / 2
  radius_nonneg := by
    unfold step leftEndpoint rightEndpoint
    positivity

lemma left_lt_right : leftEndpoint < rightEndpoint := by
  norm_num [leftEndpoint, rightEndpoint]

lemma step_pos {n : ℕ} (hn : 0 < n) : 0 < step n := by
  unfold step
  exact div_pos (sub_pos.mpr left_lt_right) (by exact_mod_cast hn)

/-- The only proof-bearing data generated for a uniform monotonicity grid. -/
structure Certificate (n : ℕ) where
  n_pos : 0 < n
  centerUpper : ∀ i : Fin n,
    deriv CurrentWindow.window (cell n i).center +
      curvatureBound * (cell n i).radius ≤ 0

private lemma endpoint_identity {n : ℕ} (hn : 0 < n) :
    leftEndpoint + (n : ℝ) * step n = rightEndpoint := by
  unfold step
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnR]
  ring

private lemma covers_of_lt_right {n : ℕ} (hn : 0 < n) {s : ℝ}
    (hleft : leftEndpoint ≤ s) (hright : s < rightEndpoint) :
    ∃ i : Fin n, (cell n i).Covers s := by
  let q : ℝ := (s - leftEndpoint) / step n
  have hstep := step_pos hn
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr hleft) hstep.le
  have hqn : q < n := by
    rw [div_lt_iff₀ hstep]
    have hid := endpoint_identity hn
    linarith
  let k : ℕ := ⌊q⌋₊
  have hklt : k < n := by
    apply (Nat.floor_lt hq0).2
    exact hqn
  let i : Fin n := ⟨k, hklt⟩
  refine ⟨i, ?_⟩
  have hkq : (k : ℝ) ≤ q := by
    exact Nat.floor_le hq0
  have hqk : q < (k : ℝ) + 1 := by
    simpa [k] using (Nat.lt_floor_add_one q)
  unfold DerivativeCell.Covers cell
  change |s - (leftEndpoint + ((k : ℝ) + 1 / 2) * step n)| ≤ step n / 2
  have hsrepr : s = leftEndpoint + q * step n := by
    dsimp [q]
    field_simp [ne_of_gt hstep]
    ring
  rw [hsrepr]
  rw [show leftEndpoint + q * step n -
      (leftEndpoint + ((k : ℝ) + 1 / 2) * step n) =
      (q - ((k : ℝ) + 1 / 2)) * step n by ring]
  rw [abs_mul, abs_of_pos hstep]
  have habs : |q - ((k : ℝ) + 1 / 2)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith

private lemma covers_right {n : ℕ} (hn : 0 < n) :
    (cell n ⟨n - 1, Nat.sub_lt hn (by omega)⟩).Covers rightEndpoint := by
  have hstep := step_pos hn
  have hid := endpoint_identity hn
  unfold DerivativeCell.Covers cell
  change |rightEndpoint -
    (leftEndpoint + (((n - 1 : ℕ) : ℝ) + 1 / 2) * step n)| ≤ step n / 2
  have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))]
    norm_num
  rw [hncast]
  rw [← hid]
  rw [show leftEndpoint + (n : ℝ) * step n -
      (leftEndpoint + ((n : ℝ) - 1 + 1 / 2) * step n) = step n / 2 by ring]
  have hhalf : 0 ≤ step n / 2 := div_nonneg hstep.le (by norm_num)
  rw [abs_of_nonneg hhalf]

def Certificate.toAwayMonotonicityTable {n : ℕ} (cert : Certificate n) :
    AwayMonotonicityTable n where
  cells := cell n
  centerUpper := cert.centerUpper
  cover := by
    intro s hs
    rw [show (1 : ℝ) / 4096 = leftEndpoint by rfl,
      show (1 : ℝ) / 2 = rightEndpoint by rfl] at hs
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact ⟨⟨n - 1, Nat.sub_lt cert.n_pos (by omega)⟩, covers_right cert.n_pos⟩
    · exact covers_of_lt_right cert.n_pos hs.1 hlt

theorem Certificate.window_antitone {n : ℕ} (cert : Certificate n) :
    AntitoneOn CurrentWindow.window (Icc (0 : ℝ) (1 / 2)) :=
  window_antitone_of_table cert.toAwayMonotonicityTable.toMonotonicityTable

end Zeta23Ext.CurrentWindowUniformGrid
