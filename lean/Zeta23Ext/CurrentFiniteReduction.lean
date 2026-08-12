/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowHybridRows
import Zeta23Ext.CurrentWindowClosedHNumeric

/-!
# Reduction of the remaining finite certificate

The strict scalar `H` bound and the endpoint range bounds are already proved.
Thus a finite hybrid monotonicity table supplies the complete window
certificate.  Pairing it with the local seven-point certificate supplies the
sole input of `CurrentEndToEnd`.
-/

noncomputable section

open Real Set

namespace Zeta23Ext.CurrentFiniteReduction

open CurrentWindow
open CurrentWindowFiniteCertificate

/-- Global antitonicity of the explicit cosine window on its positive half
produces all fields of the finite window certificate. -/
theorem windowCertificate_of_antitone
    (hanti : AntitoneOn window (Icc (0 : ℝ) (1 / 2))) :
    WindowCertificate where
  lower := by
    intro s hs
    have habs : |s| ∈ Icc (0 : ℝ) (1 / 2) :=
      ⟨abs_nonneg _, abs_le.2 ⟨by linarith [hs.1], hs.2⟩⟩
    have hhalf := hanti habs (right_mem_Icc.mpr (by norm_num)) habs.2
    have heq : window |s| = window s := by
      rcases le_or_gt 0 s with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, window_even]
    rw [heq] at hhalf
    exact window_half_lower.trans hhalf
  upper := by
    intro s hs
    have habs : |s| ∈ Icc (0 : ℝ) (1 / 2) :=
      ⟨abs_nonneg _, abs_le.2 ⟨by linarith [hs.1], hs.2⟩⟩
    have hzero := hanti (left_mem_Icc.mpr (by norm_num)) habs (abs_nonneg _)
    have heq : window |s| = window s := by
      rcases le_or_gt 0 s with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, window_even]
    rw [heq] at hzero
    exact hzero.trans window_zero_le_one
  even := window_even
  nonincreasing := hanti
  H_lower := by
    rw [H_eq_closedH]
    exact CurrentWindowClosedHNumeric.closedH_lower

/-- A semantic hybrid table and the local seven-point certificate are exactly
the two remaining finite objects needed by the end-to-end theorem. -/
theorem finiteWindowInputs_of_hybrid {nSecond nFirst : ℕ}
    (hlocal : LocalCertificate)
    (table : CurrentWindowHybridRows.Table nSecond nFirst) :
    FiniteWindowInputs where
  localCertificate := hlocal
  windowFacts := windowCertificate_of_antitone table.window_antitone

end Zeta23Ext.CurrentFiniteReduction
