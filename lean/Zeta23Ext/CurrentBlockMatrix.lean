/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentBlock

/-!
# Concrete matrix form of the current single-block argument

This module composes, without adding analytic assumptions beyond the one
shown in the theorem statement:

1. `Weighted.paper_window_summation_250`;
2. `SqrtProfile.block_defect_sqrt`;
3. `CurrentBlock.block_deduction`.

The Gram approximation remains guarded by `span < D`, so a block at or
beyond the exact threshold is handled by pressure alone.
-/

noncomputable section
set_option maxHeartbeats 1000000

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentBlockMatrix

open Zeta23Ext

/-- Twice the strict-upper-triangle energy of a `250 × 250` Gram block. -/
def offDiagEnergy
    (G : Matrix (Fin Weighted.blockLength) (Fin Weighted.blockLength) ℂ) : ℝ :=
  2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2

/-- The spectral `Psi` defect of a positive semidefinite `250 × 250`
Gram block. -/
def traceDefect
    (G : Matrix (Fin Weighted.blockLength) (Fin Weighted.blockLength) ℂ)
    (hG : G.PosSemidef) : ℝ :=
  ∑ i, StabilityRankTrace.Psi (hG.1.eigenvalues i)

lemma offDiagEnergy_nonneg
    (G : Matrix (Fin Weighted.blockLength) (Fin Weighted.blockLength) ℂ) :
    0 ≤ offDiagEnergy G := by
  unfold offDiagEnergy
  positivity

/-- **Exact matrix single-block inequality for the current paper.**

The local weighted certificate yields the kernel-energy inequality.  The
guarded approximation transfers it to the Gram energy only when the block
span is below `D`; for larger blocks pressure alone proves the result.  The
PSD matrix theorem supplies the sharp spectral-profile lower bound.
-/
theorem paper_block_matrix
    {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hloc : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) →
      Weighted.beta ≤ Weighted.F6 w g)
    {y : Fin Weighted.blockLength → ℝ} (hy : StrictMono y)
    {G : Matrix (Fin Weighted.blockLength) (Fin Weighted.blockLength) ℂ}
    (hG : G.PosSemidef)
    {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (happrox :
      y ⟨Weighted.blockLength - 1, by norm_num [Weighted.blockLength]⟩ -
          y ⟨0, by norm_num [Weighted.blockLength]⟩ < CurrentBlock.D →
        Aggregation.Em w y ≤ offDiagEnergy G + delta) :
    Current.R - Current.eta * delta ≤
      traceDefect G hG + Current.eta * Current.pressureCap *
        (y ⟨Weighted.blockLength - 1, by norm_num [Weighted.blockLength]⟩ -
          y ⟨0, by norm_num [Weighted.blockLength]⟩) := by
  let span : ℝ :=
    y ⟨Weighted.blockLength - 1, by norm_num [Weighted.blockLength]⟩ -
      y ⟨0, by norm_num [Weighted.blockLength]⟩
  have hspan0 : 0 ≤ span := by
    apply sub_nonneg.mpr
    apply hy.monotone
    change (0 : ℕ) ≤ Weighted.blockLength - 1
    omega
  have hkernel0 := Weighted.paper_window_summation_250 hw hloc hy
  have hkernel : Current.A ≤ Aggregation.Em w y + Current.pressureCap * span := by
    have hA : Weighted.blockTarget = Current.A := by
      norm_num [Weighted.blockTarget, Current.A]
    have hB : (3 / 1150 : ℝ) = Current.pressureCap := by
      rfl
    rw [hA, hB] at hkernel0
    exact hkernel0
  have hprofile : SqrtProfile.sqrtProfile (offDiagEnergy G) ≤ traceDefect G hG := by
    exact SqrtProfile.block_defect_sqrt hG
  apply CurrentBlock.block_deduction
    (offDiagEnergy_nonneg G) hspan0 hdelta0 hkernel
  · intro hsmall
    apply happrox
    exact hsmall
  · exact hprofile

end Zeta23Ext.CurrentBlockMatrix
