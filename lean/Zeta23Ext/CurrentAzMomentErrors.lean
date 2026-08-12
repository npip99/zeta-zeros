/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentAzMoments
import Zeta23Ext.CurrentInteriorAsymptotic

/-!
# Negligibility of the current `Az` moment errors

The exact positive-part defects extracted from `GzMoments`, the enlarged-window
boundary count, and the normalized zero-side tail are all negligible on the
`NIprime` scale.  The Frobenius estimate is discharged through the generic
square-root error lemma from `Zeta23.Assembly`.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Filter Asymptotics
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentAzMomentErrors

open Zeta23
open Zeta23.XiPrime
open Zeta23Ext.CurrentAzMoments
open Zeta23Ext.CurrentInteriorRetentionBridge
open Zeta23Ext.CurrentInteriorAsymptotic

theorem gzTraceDefect_isLittleO_NIprime
    {Z : ZeroConfig} {Pf : ℝ → Params} {kappa : ℝ}
    (hM : GzMoments Z Pf kappa) :
    gzTraceDefect Z Pf =o[atTop] (fun T => (Z.NIprime T : ℝ)) :=
  (gzTraceDefect_isLittleO_N hM).trans_isBigO
    (N_isBigO_NIprime Z)

theorem gzFrobDefect_isLittleO_NIprime
    {Z : ZeroConfig} {Pf : ℝ → Params} {kappa : ℝ}
    (hM : GzMoments Z Pf kappa) :
    gzFrobDefect Z Pf kappa =o[atTop]
      (fun T => (Z.NIprime T : ℝ)) :=
  (gzFrobDefect_isLittleO_N hM).trans_isBigO
    (N_isBigO_NIprime Z)

theorem currentTailB_isLittleO_NIprime
    {Z : ZeroConfig} {P : Params} (hR : RiemannVonMangoldt Z)
    (tail : CurrentTailData Z P) :
    tail.B =o[atTop] (fun T => (Z.NIprime T : ℝ)) := by
  have hB1 : tail.B =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 tail.tendsto_zero
  exact hB1.trans (one_isLittleO_NIprime Z hR)

theorem currentAzTraceError_isLittleO_NIprime
    {Z : ZeroConfig} {P : Params} {kappa : ℝ}
    (hR : RiemannVonMangoldt Z)
    (hM : GzMoments Z (P.atV CurrentWindow.window) kappa)
    (tail : CurrentTailData Z P) :
    currentAzTraceError Z P tail =o[atTop]
      (fun T => (Z.NIprime T : ℝ)) := by
  exact ((NII_isLittleO_NIprime Z hR).add
    (gzTraceDefect_isLittleO_NIprime hM)).add
    (currentTailB_isLittleO_NIprime hR tail)

theorem currentAzFrobError_isLittleO_NIprime
    {Z : ZeroConfig} {P : Params} {kappa : ℝ}
    (hR : RiemannVonMangoldt Z)
    (hk0 : 0 ≤ kappa)
    (hM : GzMoments Z (P.atV CurrentWindow.window) kappa)
    (tail : CurrentTailData Z P) :
    currentAzFrobError Z P kappa tail =o[atTop]
      (fun T => (Z.NIprime T : ℝ)) := by
  let Np : ℝ → ℝ := fun T => (Z.NIprime T : ℝ)
  let Df : ℝ → ℝ :=
    gzFrobDefect Z (P.atV CurrentWindow.window) kappa
  have hDf : Df =o[atTop] Np :=
    gzFrobDefect_isLittleO_NIprime hM
  have hzero : (fun _ : ℝ => (0 : ℝ)) =o[atTop] Np :=
    isLittleO_zero Np atTop
  have hraw := Assembly.err_isLittleO
    (N := Np) (R₁ := fun _ => 0) (R₂ := Df)
    (NII := fun _ => 0) (B := tail.B) (cl := fun _ => kappa)
    (K := kappa) (tendsto_NIprime_atTop Z hR)
    hzero hDf hzero tail.tendsto_zero
    (Eventually.of_forall fun _ => ⟨hk0, le_rfl⟩)
  apply hraw.congr'
  · filter_upwards [] with T
    norm_num [currentAzFrobError, Np, Df]
  · exact Eventually.of_forall fun _ => rfl

end Zeta23Ext.CurrentAzMomentErrors
