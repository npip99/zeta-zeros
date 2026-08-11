/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentAssembly
import Zeta23Ext.CurrentZeta

/-!
# Zeta specialization of the assembled current-window input

This module performs only the final identification of the abstract sequences
in `CurrentAssembly.AsymptoticInputs` with the dyadic zeta counts.  It does not
add an analytic assumption: every finite-height hypothesis and every
small-error hypothesis remains inside the supplied assembled input.
-/

noncomputable section

open Filter

namespace Zeta23Ext.CurrentZetaAssembly

open Zeta23
open Zeta23Ext

/-- Select the defect of one assembled finite-height witness when such a
witness exists, and use zero otherwise.  Only the eventual branch is consumed
below; the default makes this a total function on all real heights. -/
def selectedDefect (h : CurrentAssembly.AsymptoticInputs (atTop : Filter ℝ))
    (T : ℝ) : ℝ := by
  classical
  exact
    if hex : Nonempty (CurrentAssembly.FiniteHeightInputs
        (h.r T) (h.N T) (h.stabilityError T) (h.spanError T) (h.delta T)) then
      let hx := Classical.choice hex
      CurrentAssembly.globalDefect hx.G hx.G_posSemidef
    else
      0

/-- An assembled asymptotic input becomes the exact zeta analytic interface
once its two abstract counting sequences are identified with the simple-zero
and all-zero counts on `(T,2T]`.

The chosen defect is only bookkeeping for the existential Gram matrix already
present in `h.eventuallyHeight`; no choice is used to assert a new fact.
-/
def toCurrentZetaAnalyticInputs
    (h : CurrentAssembly.AsymptoticInputs (atTop : Filter ℝ))
    (hr : ∀ T, h.r T = N0simple T (2 * T))
    (hN : ∀ T, h.N T = (Ncount T (2 * T) : ℝ)) :
    Current.CurrentZetaAnalyticInputs where
  defect := selectedDefect h
  stabilityError := h.stabilityError
  blockError := fun T =>
    CurrentAssembly.assembledBlockError (h.r T) (h.delta T) (h.spanError T)
  eventuallyData := by
    filter_upwards [h.eventuallyHeight] with T height
    let chosen := Classical.choice height
    have hchosen := chosen.toWeightedBlockDefectData
    have hselected : selectedDefect h T =
        CurrentAssembly.globalDefect chosen.G chosen.G_posSemidef := by
      unfold selectedDefect
      rw [dif_pos height]
    rw [hselected]
    simpa [chosen, hr T, hN T] using hchosen
  errorsAreSmall := by
    intro eps heps
    filter_upwards [h.errorsAreSmall eps heps] with T hsmall
    simpa [hN T] using hsmall

/-- Eventual exact-rational zeta target obtained from the assembled input. -/
theorem zeta_target_eventually
    (h : CurrentAssembly.AsymptoticInputs (atTop : Filter ℝ))
    (hr : ∀ T, h.r T = N0simple T (2 * T))
    (hN : ∀ T, h.N T = (Ncount T (2 * T) : ℝ)) :
    ∀ᶠ T in atTop,
      Current.target * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  Current.zeta_conditional_target_eventually
    (toCurrentZetaAnalyticInputs h hr hN)

/-- Threshold form of the same conditional `0.673195` dyadic conclusion. -/
theorem zeta_target
    (h : CurrentAssembly.AsymptoticInputs (atTop : Filter ℝ))
    (hr : ∀ T, h.r T = N0simple T (2 * T))
    (hN : ∀ T, h.N T = (Ncount T (2 * T) : ℝ)) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      Current.target * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  Current.zeta_conditional_target (toCurrentZetaAnalyticInputs h hr hN)

/-- Cumulative exact-target epsilon form, using the upstream unconditional
Riemann--von Mangoldt theorem rather than requiring it from the caller. -/
theorem zeta_target_cumulative
    (h : CurrentAssembly.AsymptoticInputs (atTop : Filter ℝ))
    (hr : ∀ T, h.r T = N0simple T (2 * T))
    (hN : ∀ T, h.N T = (Ncount T (2 * T) : ℝ)) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Current.target - eps) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  Current.zeta_conditional_target_cumulative_unconditional_rvm
    (toCurrentZetaAnalyticInputs h hr hN)

end Zeta23Ext.CurrentZetaAssembly
