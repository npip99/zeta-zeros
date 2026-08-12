/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentEndToEnd
import Zeta23Ext.CurrentFiniteReduction
import Zeta23Ext.CurrentWindowMonotonicityTable

/-!
# Final theorem from the two concrete finite artifacts

This module exposes the exact final integration point for certificate
generation.  There are no analytic hypotheses: a checked local seven-point
certificate and a finite semantic hybrid monotonicity table imply the
cumulative zeta-zero bound.
-/

namespace Zeta23Ext.CurrentFiniteCapstone

open Zeta23

/-- Exact dyadic target from the two remaining finite artifacts. -/
theorem exists_current_zeta_dyadic_target_of_hybrid {nSecond nFirst : ℕ}
    (hlocal : CurrentWindow.LocalCertificate)
    (table : CurrentWindowHybridRows.Table nSecond nFirst) :
    ∃ P : Params, P.Valid ∧ 1 / 2 ≤ P.lam ∧ P.lam < 1 ∧
      ∀ᶠ T in Filter.atTop,
        Current.target * (Ncount T (2 * T) : ℝ) ≤
          (N0simple T (2 * T) : ℝ) := by
  exact CurrentEndToEnd.exists_current_zeta_dyadic_target
    (CurrentFiniteReduction.finiteWindowInputs_of_hybrid hlocal table)

/-- Cumulative `0.673195` target from the two remaining finite artifacts. -/
theorem current_zeta_cumulative_target_of_hybrid {nSecond nFirst : ℕ}
    (hlocal : CurrentWindow.LocalCertificate)
    (table : CurrentWindowHybridRows.Table nSecond nFirst) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Current.target - eps) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  exact CurrentEndToEnd.current_zeta_cumulative_target
    (CurrentFiniteReduction.finiteWindowInputs_of_hybrid hlocal table)

/-- Exact dyadic target from the sole remaining local search certificate. -/
theorem exists_current_zeta_dyadic_target
    (hlocal : CurrentWindow.LocalCertificate) :
    ∃ P : Params, P.Valid ∧ 1 / 2 ≤ P.lam ∧ P.lam < 1 ∧
      ∀ᶠ T in Filter.atTop,
        Current.target * (Ncount T (2 * T) : ℝ) ≤
          (N0simple T (2 * T) : ℝ) := by
  exact exists_current_zeta_dyadic_target_of_hybrid hlocal
    CurrentWindowMonotonicityTable.table

/-- Cumulative `0.673195` theorem from the sole remaining local search
certificate.  All window facts, including monotonicity and the strict scalar
`H` bound, are discharged by kernel-checked finite arithmetic. -/
theorem current_zeta_cumulative_target
    (hlocal : CurrentWindow.LocalCertificate) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Current.target - eps) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  exact current_zeta_cumulative_target_of_hybrid hlocal
    CurrentWindowMonotonicityTable.table

end Zeta23Ext.CurrentFiniteCapstone
