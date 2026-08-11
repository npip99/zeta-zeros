/-
Zeta-counting specialization of the conditional current-result capstone.

There is intentionally no unconditional theorem in this file.  The structure
`CurrentZetaAnalyticInputs` is the remaining interface to be discharged by the
current ramped window, weighted seven-point certificate, Gram asymptotics,
pinching, endpoint deletion, and span bookkeeping.
-/
import Zeta23Ext.CurrentCapstone
import Zeta23.Main
import Zeta23.GammaFacts.Complete
import Zeta23.RvM.Statement

noncomputable section

open Filter

namespace Zeta23Ext.Current

open Zeta23

/-- The current analytic/block interface at zeta height `T`.

The defect and the two independent error functions are deliberately exposed.
This prevents an older hard-coded Montgomery--Taylor theorem from being
mistaken for a discharge of the present weighted-window hypotheses. -/
structure CurrentZetaAnalyticInputs where
  defect : ℝ → ℝ
  stabilityError : ℝ → ℝ
  blockError : ℝ → ℝ
  eventuallyData : ∀ᶠ T in atTop,
    WeightedBlockDefectData
      (N0simple T (2 * T) : ℝ)
      (Ncount T (2 * T) : ℝ)
      (defect T) (stabilityError T) (blockError T)
  errorsAreSmall : ∀ eps > 0, ∀ᶠ T in atTop,
    stabilityError T + blockError T ≤
      (1 - R / (m : ℝ)) * eps * (Ncount T (2 * T) : ℝ)

/-- Filter-native zeta specialization of the exact headline capstone. -/
theorem zeta_conditional_capstone_eventually (h : CurrentZetaAnalyticInputs) :
    ∀ eps > 0, ∀ᶠ T in atTop,
      (headline - eps) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  exact conditional_capstone h.eventuallyData h.errorsAreSmall

/-- Conventional epsilon/threshold presentation of the same conditional result. -/
theorem zeta_conditional_capstone (h : CurrentZetaAnalyticInputs) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (headline - eps) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  intro eps heps
  have hev := zeta_conditional_capstone_eventually h eps heps
  exact Filter.eventually_atTop.1 hev

/-- Because the printed rational target is strictly below `headline`, the
aggregate `o(N)` error can be absorbed once and for all. -/
theorem zeta_conditional_target_eventually (h : CurrentZetaAnalyticInputs) :
    ∀ᶠ T in atTop,
      target * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  exact conditional_target h.eventuallyData h.errorsAreSmall

/-- Threshold form at the exact rational target `673195/10^6`. -/
theorem zeta_conditional_target (h : CurrentZetaAnalyticInputs) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      target * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  exact Filter.eventually_atTop.1 (zeta_conditional_target_eventually h)

/-- Epsilon form at the rational target, used by the generic dyadic wrapper. -/
theorem zeta_conditional_target_epsilon (h : CurrentZetaAnalyticInputs) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (target - eps) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  intro eps heps
  obtain ⟨T₀, hT₀⟩ := zeta_conditional_target h
  refine ⟨T₀, fun T hT => ?_⟩
  have htarget := hT₀ T hT
  have hN : (0 : ℝ) ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- Conditional cumulative consequence.  Besides the current analytic inputs,
this uses only the existing generic dyadic lemma and Riemann--von Mangoldt input.
The loss of an arbitrary `eps` is unavoidable when the fixed bottom interval is
discarded in dyadic summation. -/
theorem zeta_conditional_target_cumulative
    (h : CurrentZetaAnalyticInputs)
    (hRvM : RiemannVonMangoldt (zetaZeros zetaSeam)) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (target - eps) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  exact cumulative_of_dyadic zetaSeam hRvM
    (fun _ _ _ => N0simple_add' zetaSeam)
    (zeta_conditional_target_epsilon h)

/-- The same cumulative theorem with Riemann--von Mangoldt discharged by the
unconditional zeta development in the pinned upstream package. -/
theorem zeta_conditional_target_cumulative_unconditional_rvm
    (h : CurrentZetaAnalyticInputs) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (target - eps) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  exact zeta_conditional_target_cumulative h
    (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts)

end Zeta23Ext.Current
