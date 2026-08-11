/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowInterface
import Zeta23Ext.CurrentBlockMatrix
import Zeta23Ext.CurrentAveraging
import Zeta23Ext.CurrentCapstone

/-!
# Assembly interface for the current weighted-window deduction

This file joins the finite window inputs, the guarded single-block matrix
theorem, offset averaging, and the algebraic capstone.  It does not discharge
the external Arb certificates or any zeta-specific analytic statement.

At one height a caller still supplies the retained ordinates and Gram matrix,
the guarded Gram approximation on every full block, a total-span comparison,
and the stability seam.  From those data Lean constructs the exact
`WeightedBlockDefectData` consumed by `CurrentCapstone`.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Matrix Finset Filter
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentAssembly

open Zeta23Ext
open Zeta23Ext.Stability

/-- The spectral defect of a retained Gram matrix. -/
def globalDefect {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosSemidef) : ℝ :=
  ∑ j, StabilityRankTrace.Psi (hG.1.eigenvalues j)

/-- The explicit error charged by the finite offset average.

The three summands are respectively the incomplete-block endpoint loss, the
uniform per-block Gram-approximation loss, and the error in replacing the
normalized total span by the ambient zero count. -/
def assembledBlockError (r : ℕ) (delta spanError : ℝ) : ℝ :=
  (249 / 250 : ℝ) * Current.R +
    (Current.eta * delta / 250) * (r : ℝ) +
    Current.eta * Current.pressureCap * (249 / 250 : ℝ) * spanError

/-- All finite and analytic data needed at one height.

`finiteWindow` contains the two external finite certificates.  The guarded
approximation is deliberately stated only for blocks of span `< CurrentBlock.D`;
`paper_block_matrix` handles the complementary large-span branch by pressure.
The `spanControl` and `stabilitySeam` fields remain analytic inputs. -/
structure FiniteHeightInputs
    (r : ℕ) (N stabilityError spanError delta : ℝ) where
  finiteWindow : CurrentWindow.FiniteWindowInputs
  r_pos : 0 < r
  N_nonneg : 0 ≤ N
  delta_nonneg : 0 ≤ delta
  delta_small : Current.eta * delta ≤ Current.R
  spanError_nonneg : 0 ≤ spanError
  y : Fin r → ℝ
  y_strictMono : StrictMono y
  G : Matrix (Fin r) (Fin r) ℂ
  G_posSemidef : G.PosSemidef
  block_strictMono :
    ∀ {K t : ℕ} (hKt : t + K * Current.m ≤ r) (c : Fin K),
      StrictMono (fun i : Fin Current.m => y (blockEmb hKt c i))
  guardedGramApprox :
    ∀ {K t : ℕ} (hKt : t + K * Current.m ≤ r) (c : Fin K),
      let e := blockEmb hKt c
      y (e ⟨Current.m - 1, by norm_num [Current.m]⟩) -
          y (e ⟨0, by norm_num [Current.m]⟩) < CurrentBlock.D →
        Aggregation.Em CurrentWindow.weight (fun i => y (e i)) ≤
          CurrentBlockMatrix.offDiagEnergy (G.submatrix e e) + delta
  spanControl :
    y ⟨r - 1, by omega⟩ - y ⟨0, r_pos⟩ ≤ N + spanError
  stabilitySeam :
    Current.Hcert * N + globalDefect G G_posSemidef - stabilityError ≤ (r : ℝ)

/-- The guarded approximation plus both finite certificates imply the block
bound required by offset averaging. -/
theorem FiniteHeightInputs.block_bound
    {r : ℕ} {N stabilityError spanError delta : ℝ}
    (h : FiniteHeightInputs r N stabilityError spanError delta) :
    ∀ {K t : ℕ} (hKt : t + K * Current.m ≤ r) (c : Fin K),
      Current.R - Current.eta * delta ≤
        ∑ i, StabilityRankTrace.Psi
          ((h.G_posSemidef.submatrix (blockEmb hKt c)).1.eigenvalues i) +
          Current.eta * Current.pressureCap *
            (h.y (blockEmb hKt c ⟨Current.m - 1, by norm_num [Current.m]⟩) -
              h.y (blockEmb hKt c ⟨0, by norm_num [Current.m]⟩)) := by
  intro K t hKt c
  have hpaper := CurrentBlockMatrix.paper_block_matrix
    CurrentWindow.weight_nonneg h.finiteWindow.localCertificate
    (h.block_strictMono hKt c)
    (h.G_posSemidef.submatrix (blockEmb hKt c)) h.delta_nonneg
    (h.guardedGramApprox hKt c)
  convert hpaper using 1 <;>
    simp [CurrentBlockMatrix.traceDefect, Current.m, Weighted.blockLength]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1

/-- Exact normalized offset average assembled from the single-block theorem. -/
theorem FiniteHeightInputs.averaged
    {r : ℕ} {N stabilityError spanError delta : ℝ}
    (h : FiniteHeightInputs r N stabilityError spanError delta) :
    (Current.R / 250) * (r : ℝ) - (249 / 250) * Current.R
        - (Current.eta * delta / 250) * (r : ℝ)
        - Current.eta * Current.pressureCap * (249 / 250) *
          (h.y ⟨r - 1, by have hr := h.r_pos; omega⟩ - h.y ⟨0, h.r_pos⟩)
      ≤ globalDefect h.G h.G_posSemidef := by
  exact CurrentAveraging.current_averaged_defect_normalized
    h.r_pos h.delta_nonneg h.delta_small h.y_strictMono h.G_posSemidef h.block_bound

/-- The exact `WeightedBlockDefectData` expected by `CurrentCapstone`.

No analytic fact is added here: the proof only substitutes the span comparison
into the normalized offset average and records the already-supplied stability
seam. -/
theorem FiniteHeightInputs.toWeightedBlockDefectData
    {r : ℕ} {N stabilityError spanError delta : ℝ}
    (h : FiniteHeightInputs r N stabilityError spanError delta) :
    Current.WeightedBlockDefectData
      (r : ℝ) N (globalDefect h.G h.G_posSemidef) stabilityError
      (assembledBlockError r delta spanError) := by
  refine ⟨h.N_nonneg, h.stabilitySeam, ?_⟩
  have havg := h.averaged
  have hcoeff0 : 0 ≤ Current.eta * Current.pressureCap * (249 / 250 : ℝ) := by
    exact mul_nonneg (mul_nonneg Current.eta_pos.le Current.pressureCap_pos.le) (by norm_num)
  have hspan := mul_le_mul_of_nonneg_left h.spanControl hcoeff0
  norm_num [Current.m, assembledBlockError] at havg ⊢
  linarith

/-- One-height target theorem after the caller bounds the two remaining error
terms. -/
theorem FiniteHeightInputs.target_bound
    {r : ℕ} {N stabilityError spanError delta : ℝ}
    (h : FiniteHeightInputs r N stabilityError spanError delta)
    (herror : stabilityError + assembledBlockError r delta spanError ≤
      Current.targetErrorRate * N) :
    Current.target * N ≤ (r : ℝ) := by
  exact h.toWeightedBlockDefectData.target_bound herror

/-- Filter-level assembly.  This is the smallest generic interface immediately
before the zeta-specific identification `r = N0simple(T,2T)` and
`N = Ncount(T,2T)`.  Each `FiniteHeightInputs` value still contains the Arb
certificates and every analytic hypothesis listed above. -/
structure AsymptoticInputs {X : Type*} (l : Filter X) where
  r : X → ℕ
  N : X → ℝ
  stabilityError : X → ℝ
  spanError : X → ℝ
  delta : X → ℝ
  eventuallyHeight : ∀ᶠ x in l,
    Nonempty (FiniteHeightInputs (r x) (N x) (stabilityError x) (spanError x) (delta x))
  errorsAreSmall : ∀ eps > 0, ∀ᶠ x in l,
    stabilityError x + assembledBlockError (r x) (delta x) (spanError x) ≤
      (1 - Current.R / (Current.m : ℝ)) * eps * N x

/-- Direct use of the algebraic capstone after finite-height assembly. -/
theorem AsymptoticInputs.capstone
    {X : Type*} {l : Filter X} (h : AsymptoticInputs l) :
    ∀ eps > 0, ∀ᶠ x in l,
      (Current.headline - eps) * h.N x ≤ (h.r x : ℝ) := by
  intro eps heps
  filter_upwards [h.eventuallyHeight, h.errorsAreSmall eps heps] with x hx herr
  obtain ⟨hx⟩ := hx
  exact hx.toWeightedBlockDefectData.epsilon_form herr

/-- Rational-target specialization of the assembled asymptotic theorem. -/
theorem AsymptoticInputs.target
    {X : Type*} {l : Filter X} (h : AsymptoticInputs l) :
    ∀ᶠ x in l, Current.target * h.N x ≤ (h.r x : ℝ) := by
  have hmargin : 0 < Current.headline - Current.target :=
    sub_pos.mpr Current.target_lt_headline
  filter_upwards [h.eventuallyHeight,
    h.errorsAreSmall (Current.headline - Current.target) hmargin] with x hx herr
  obtain ⟨hx⟩ := hx
  have hout := hx.toWeightedBlockDefectData.epsilon_form herr
  simpa only [sub_sub_cancel] using hout

end Zeta23Ext.CurrentAssembly
