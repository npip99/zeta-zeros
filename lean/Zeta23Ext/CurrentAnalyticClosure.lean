/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentAzMomentErrors
import Zeta23Ext.CurrentZetaEndpoint

/-!
# Current-window analytic closure

This module connects the zeta-native `GzMoments` theorem to the concrete
interior retained family.  In particular, the two `Az` errors supplied to the
asymptotic assembler are the explicit functions proved negligible in
`CurrentAzMomentErrors`; no abstract moment-error premise remains.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Filter Asymptotics
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentAnalyticClosure

open Zeta23
open Zeta23.XiPrime
open Zeta23Ext.CurrentAzMoments
open Zeta23Ext.CurrentAzMomentErrors
open Zeta23Ext.CurrentInteriorAsymptotic

/-- The interior compression is literally a subtype of the canonical retained
simple-zero family. -/
theorem currentInteriorCount_le_N0s
    (Z : ZeroConfig) (P : Params) (T : ℝ) :
    currentInteriorCount Z P T ≤ Z.N0s T (2 * T) := by
  have hsub : currentInteriorCount Z P T ≤
      Fintype.card (CurrentCentralSelection.RetainedAtom Z
        (P.atV CurrentWindow.window T) T ZeroSide.phiHatConj) := by
    simpa [currentInteriorCount] using
      (Fintype.card_subtype_le
        (CurrentInteriorRetention.IsInteriorIndex Z
          (P.atV CurrentWindow.window T) T ZeroSide.phiHatConj))
  simpa only [CurrentCentralSelection.card_retainedAtom] using hsub

/-- Generic closure from current-window `Gz` moments to the fully assembled
interior-count lower bound. -/
theorem currentInterior_target_of_GzMoments
    {Z : ZeroConfig} {P : Params} {kappa : ℝ}
    (hP : P.Valid) (hlam : P.lam < 1)
    (hR : RiemannVonMangoldt Z)
    (hcert : CurrentWindow.WindowCertificate)
    (hfinite : CurrentWindow.FiniteWindowInputs)
    (hk0 : 0 ≤ kappa) (hk : kappa ≤ 2 - Current.Hcert)
    (hM : GzMoments Z (P.atV CurrentWindow.window) kappa) :
    ∀ᶠ T in atTop, Current.target * (Z.NIprime T : ℝ) ≤
      (currentInteriorCount Z P T : ℝ) := by
  obtain ⟨tail⟩ := exists_currentTailData hP hlam hR hcert
  apply currentInterior_target_of_AzMoments hP hlam hR hcert hfinite
    (currentAzTraceError_isLittleO_NIprime hR hM tail)
    (currentAzFrobError_isLittleO_NIprime hR hk0 hM tail)
  exact eventually_currentAzMomentPremise hk0 hk hM tail

/-- The current zeta endpoint supplies a fixed valid `lam < 1` and a strict
moment constant, so the analytic closure has no remaining zeta-side analytic
premise.  The finite certificate input remains explicit because it is the
repository's documented verifier-soundness boundary. -/
theorem exists_current_zeta_interior_target_of_Hcert_lt
    (hcert : CurrentWindow.WindowCertificate)
    (hstrict : CurrentWindow.Hcert < CurrentWindow.H CurrentWindow.window)
    (hfinite : CurrentWindow.FiniteWindowInputs) :
    ∃ P : Params, P.Valid ∧ 1 / 2 ≤ P.lam ∧ P.lam < 1 ∧
      ∀ᶠ T in atTop,
        Current.target * (zetaZeroConfig.NIprime T : ℝ) ≤
          (currentInteriorCount zetaZeroConfig P T : ℝ) := by
  obtain ⟨P, hP, hlam0, hlam1, hM, hk⟩ :=
    CurrentZetaEndpoint.exists_current_zeta_moment_params_of_Hcert_lt
      hcert hstrict
  refine ⟨P, hP, hlam0, hlam1, ?_⟩
  apply currentInterior_target_of_GzMoments hP hlam1
    Zeta23.riemannVonMangoldt_zeta hcert hfinite
  · exact inv_nonneg.mpr
      (CurrentZetaNative.current_cWin_id_pos hP hcert).le
  · exact hk.le
  · exact hM

/-- Transfer the retained interior target to the actual dyadic simple-zero
count.  The switch from `NIprime` to the smaller dyadic total count loses
nothing. -/
theorem exists_current_zeta_dyadic_target_of_Hcert_lt
    (hcert : CurrentWindow.WindowCertificate)
    (hstrict : CurrentWindow.Hcert < CurrentWindow.H CurrentWindow.window)
    (hfinite : CurrentWindow.FiniteWindowInputs) :
    ∃ P : Params, P.Valid ∧ 1 / 2 ≤ P.lam ∧ P.lam < 1 ∧
      ∀ᶠ T in atTop,
        Current.target * (Zeta23.Ncount T (2 * T) : ℝ) ≤
          (Zeta23.N0simple T (2 * T) : ℝ) := by
  obtain ⟨P, hP, hlam0, hlam1, hint⟩ :=
    exists_current_zeta_interior_target_of_Hcert_lt hcert hstrict hfinite
  refine ⟨P, hP, hlam0, hlam1, ?_⟩
  filter_upwards [hint, eventually_ge_atTop (0 : ℝ)] with T htarget hT
  have hNle : (zetaZeroConfig.N T (2 * T) : ℝ) ≤
      (zetaZeroConfig.NIprime T : ℝ) := by
    exact_mod_cast (show zetaZeroConfig.N T (2 * T) ≤
        zetaZeroConfig.NIprime T by
      rw [Assembly.NIprime_eq zetaZeroConfig hT]
      exact Nat.le_add_right _ _)
  have hleft : Current.target *
      (zetaZeroConfig.N T (2 * T) : ℝ) ≤
      Current.target * (zetaZeroConfig.NIprime T : ℝ) :=
    mul_le_mul_of_nonneg_left hNle (by norm_num [Current.target])
  have hright : (currentInteriorCount zetaZeroConfig P T : ℝ) ≤
      (zetaZeroConfig.N0s T (2 * T) : ℝ) := by
    exact_mod_cast currentInteriorCount_le_N0s zetaZeroConfig P T
  simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using
    hleft.trans (htarget.trans hright)

/-- Fully zeta-specialized cumulative theorem.  Apart from the documented
finite-certificate soundness boundary, this exposes only the strict endpoint
inequality used to choose one fixed `lam < 1`; all zeta-side analysis, tail
transfer, Gram limit, deletion estimates, and error assembly are discharged. -/
theorem current_zeta_cumulative_target_of_Hcert_lt
    (hcert : CurrentWindow.WindowCertificate)
    (hstrict : CurrentWindow.Hcert < CurrentWindow.H CurrentWindow.window)
    (hfinite : CurrentWindow.FiniteWindowInputs) :
    ∀ eps > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Current.target - eps) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0simple 0 T := by
  obtain ⟨P, hP, hlam0, hlam1, hdy⟩ :=
    exists_current_zeta_dyadic_target_of_Hcert_lt
      hcert hstrict hfinite
  apply Zeta23.cumulative_of_dyadic zetaSeam
    Zeta23.riemannVonMangoldt_zeta
    (fun _ _ _ => Zeta23.N0simple_add' Zeta23.zetaSeam)
  intro eps heps
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hdy
  refine ⟨T₀, fun T hT => ?_⟩
  have htarget := hT₀ T hT
  have hN : (0 : ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  nlinarith

end Zeta23Ext.CurrentAnalyticClosure
