/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentAnalyticClosure
import Zeta23Ext.CurrentWindowClosedHNumeric

/-!
# Current theorem reduced to the finite certificate

The strict endpoint inequality is now proved inside Lean.  Consequently the
only remaining argument to the current zeta theorem is the finite-window
certificate: the local seven-point inequality together with the finite
window range and monotonicity facts.
-/

open Filter

namespace Zeta23Ext.CurrentEndToEnd

open Zeta23

/-- The exact dyadic target, conditional only on the finite numerical
certificate being replayed in Lean. -/
theorem exists_current_zeta_dyadic_target
    (hfinite : CurrentWindow.FiniteWindowInputs) :
    ∃ P : Params, P.Valid ∧ 1 / 2 ≤ P.lam ∧ P.lam < 1 ∧
      ∀ᶠ T in atTop,
        Current.target * (Zeta23.Ncount T (2 * T) : ℝ) ≤
          (Zeta23.N0simple T (2 * T) : ℝ) := by
  exact CurrentAnalyticClosure.exists_current_zeta_dyadic_target_of_Hcert_lt
    hfinite.windowFacts CurrentWindowClosedHNumeric.Hcert_lt_H_window hfinite

/-- The cumulative simple-zero lower bound, conditional only on replaying the
finite numerical certificate in Lean. -/
theorem current_zeta_cumulative_target
    (hfinite : CurrentWindow.FiniteWindowInputs) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Current.target - eps) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0simple 0 T := by
  exact CurrentAnalyticClosure.current_zeta_cumulative_target_of_Hcert_lt
    hfinite.windowFacts CurrentWindowClosedHNumeric.Hcert_lt_H_window hfinite

end Zeta23Ext.CurrentEndToEnd
