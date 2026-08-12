/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentInteriorAnalyticPackage

/-!
# From current `Gz` moments to concrete central `Az` moments

This module packages the exact positive-part errors implicit in the
epsilon-form `GzMoments`, then transfers across the proved `Ez` tail package.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Filter Asymptotics
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentAzMoments

open Zeta23
open Zeta23.XiPrime
open Zeta23Ext.CurrentCentralSimple
open Zeta23Ext.CurrentAnalyticInstantiation

def gzTraceDefect (Z : ZeroConfig) (Pf : ℝ → Params) (T : ℝ) : ℝ :=
  max 0 ((Z.N T (2 * T) : ℝ) -
    RHLinalg.rtrace ((Pf T).hat T (Z.Gz (Pf T) T)))

def gzFrobDefect (Z : ZeroConfig) (Pf : ℝ → Params)
    (kappa : ℝ) (T : ℝ) : ℝ :=
  max 0 (RHLinalg.frobSq ((Pf T).hat T (Z.Gz (Pf T) T)) -
    kappa * (Z.N T (2 * T) : ℝ))

lemma gzTraceDefect_nonneg (Z : ZeroConfig) (Pf : ℝ → Params) (T : ℝ) :
    0 ≤ gzTraceDefect Z Pf T := le_max_left _ _

lemma gzFrobDefect_nonneg (Z : ZeroConfig) (Pf : ℝ → Params)
    (kappa T : ℝ) : 0 ≤ gzFrobDefect Z Pf kappa T := le_max_left _ _

theorem gzTraceDefect_isLittleO_N
    {Z : ZeroConfig} {Pf : ℝ → Params} {kappa : ℝ}
    (hM : GzMoments Z Pf kappa) :
    gzTraceDefect Z Pf =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  rw [isLittleO_iff]
  intro c hc
  have htr := hM.1 c hc
  filter_upwards [htr] with T hT
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (gzTraceDefect_nonneg Z Pf T), abs_of_nonneg hN]
  unfold gzTraceDefect
  rw [max_le_iff]
  constructor
  · positivity
  · linarith

theorem gzFrobDefect_isLittleO_N
    {Z : ZeroConfig} {Pf : ℝ → Params} {kappa : ℝ}
    (hM : GzMoments Z Pf kappa) :
    gzFrobDefect Z Pf kappa =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)) := by
  rw [isLittleO_iff]
  intro c hc
  have hfr := hM.2 c hc
  filter_upwards [hfr] with T hT
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (gzFrobDefect_nonneg Z Pf kappa T), abs_of_nonneg hN]
  unfold gzFrobDefect
  rw [max_le_iff]
  constructor
  · positivity
  · linarith

/-- Canonical current tail size from the generic zero-side package. -/
structure CurrentTailData (Z : ZeroConfig) (P : Params) where
  B : ℝ → ℝ
  tail : ∀ᶠ T in atTop,
    Assembly.TailInputs Z (P.atV CurrentWindow.window T) T
      (B T * ((P.atV CurrentWindow.window T).a T *
        (P.atV CurrentWindow.window T).L T))
  nonneg : ∀ᶠ T in atTop, 0 ≤ B T
  den_pos : ∀ᶠ T in atTop, 0 <
    (P.atV CurrentWindow.window T).a T *
      (P.atV CurrentWindow.window T).L T
  tendsto_zero : Tendsto B atTop (nhds 0)

/-- Extract tail data with the normalized `B=theta/(aL)` as its primary
field. -/
theorem exists_currentTailData
    {Z : ZeroConfig} {P : Params} (hP : P.Valid) (hlam : P.lam < 1)
    (hR : RiemannVonMangoldt Z)
    (hcert : CurrentWindow.WindowCertificate) :
    Nonempty (CurrentTailData Z P) := by
  have hW := currentWindowZeroSide_of_certificate hP hR hcert
  obtain ⟨theta, htail, hB0, hBto⟩ :=
    XiPrime.family_tail_package Z P hP hlam hW
  let B : ℝ → ℝ := fun T => theta T /
    ((P.atV CurrentWindow.window T).a T *
      (P.atV CurrentWindow.window T).L T)
  have hdenE : ∀ᶠ T in atTop, 0 <
      (P.atV CurrentWindow.window T).a T *
        (P.atV CurrentWindow.window T).L T := by
    filter_upwards [hW.a_half,
      (Params.tendsto_L_of_valid hP).eventually_gt_atTop 0] with T ha hL
    simp only [Params.atV_L]
    positivity
  refine ⟨⟨B, ?_, hB0, hdenE, hBto⟩⟩
  filter_upwards [htail, hW.a_half,
    (Params.tendsto_L_of_valid hP).eventually_gt_atTop 0] with T hT ha hL
  have hden : 0 < (P.atV CurrentWindow.window T).a T *
      (P.atV CurrentWindow.window T).L T := by
    simp only [Params.atV_L]
    positivity
  convert hT using 1
  dsimp [B]
  field_simp

def currentAzTraceError (Z : ZeroConfig) (P : Params)
    (tail : CurrentTailData Z P) (T : ℝ) : ℝ :=
  (Assembly.NII Z T : ℝ) +
    gzTraceDefect Z (P.atV CurrentWindow.window) T + tail.B T

def currentAzFrobError (Z : ZeroConfig) (P : Params) (kappa : ℝ)
    (tail : CurrentTailData Z P) (T : ℝ) : ℝ :=
  let Np := (Z.NIprime T : ℝ)
  let D := gzFrobDefect Z (P.atV CurrentWindow.window) kappa T
  D + tail.B T * (4 + 2 * Real.sqrt (kappa * Np + D) + tail.B T)

theorem eventually_currentAzMomentPremise
    {Z : ZeroConfig} {P : Params} {kappa : ℝ}
    (hk0 : 0 ≤ kappa) (hk : kappa ≤ 2 - Current.Hcert)
    (hM : GzMoments Z (P.atV CurrentWindow.window) kappa)
    (tail : CurrentTailData Z P) :
    ∀ᶠ T in atTop,
      CentralAzMomentPremise Z (P.atV CurrentWindow.window T) T
        (Z.NIprime T : ℝ) (currentAzTraceError Z P tail T)
        (currentAzFrobError Z P kappa tail T) := by
  filter_upwards [tail.tail, tail.nonneg, tail.den_pos,
    eventually_ge_atTop (0 : ℝ)] with T htail hB hden hT
  obtain ⟨B0, hB00, htr, hfr, hB0le⟩ := htail.hat
  let Q := P.atV CurrentWindow.window T
  let N := (Z.N T (2 * T) : ℝ)
  let Np := (Z.NIprime T : ℝ)
  let Dt := gzTraceDefect Z (P.atV CurrentWindow.window) T
  let Df := gzFrobDefect Z (P.atV CurrentWindow.window) kappa T
  have hNI : Np = N + (Assembly.NII Z T : ℝ) := by
    dsimp [N, Np]
    exact_mod_cast Assembly.NIprime_eq Z hT
  have htrace0 : N - Dt ≤ RHLinalg.rtrace (Q.hat T (Z.Gz Q T)) := by
    have hDt := le_max_right 0
      (N - RHLinalg.rtrace (Q.hat T (Z.Gz Q T)))
    change N - RHLinalg.rtrace (Q.hat T (Z.Gz Q T)) ≤ Dt at hDt
    linarith
  have htrace : Np - ((Assembly.NII Z T : ℝ) + Dt) ≤
      RHLinalg.rtrace (Q.hat T (Z.Gz Q T)) := by
    rw [hNI]
    linarith
  have hbase : RHLinalg.frobSq (Q.hat T (Z.Gz Q T)) ≤
      kappa * N + Df := by
    have hDf := le_max_right 0
      (RHLinalg.frobSq (Q.hat T (Z.Gz Q T)) - kappa * N)
    change RHLinalg.frobSq (Q.hat T (Z.Gz Q T)) - kappa * N ≤ Df at hDf
    linarith
  have hNNp : N ≤ Np := by
    rw [hNI]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hkNNp : kappa * N ≤ (2 - Current.Hcert) * Np := by
    calc
      kappa * N ≤ kappa * Np := mul_le_mul_of_nonneg_left hNNp hk0
      _ ≤ (2 - Current.Hcert) * Np :=
        mul_le_mul_of_nonneg_right hk (by
          dsimp [Np]
          positivity)
  have hfrob : RHLinalg.frobSq (Q.hat T (Z.Gz Q T)) ≤
      (2 - Current.Hcert) * Np + Df := hbase.trans (by linarith)
  have hB0le' : B0 ≤ tail.B T := by
    have hdenQ : Q.a T * Q.L T ≠ 0 := by
      simpa [Q] using ne_of_gt hden
    calc
      B0 ≤ tail.B T * (Q.a T * Q.L T) / (Q.a T * Q.L T) := by
        simpa [Q] using hB0le
      _ = tail.B T := by
        rw [mul_comm (tail.B T) (Q.a T * Q.L T)]
        exact mul_div_cancel_left₀ _ hdenQ
  have hfr' : RHLinalg.frobSq (Q.hat T (Z.Ez Q T)) ≤ tail.B T ^ 2 :=
    hfr.trans ((sq_le_sq₀ hB00 hB).2 hB0le')
  have htr' : |RHLinalg.rtrace (Q.hat T (Z.Ez Q T))| ≤ tail.B T :=
    htr.trans hB0le'
  have hcentral := CentralAzMomentPremise.ofGzTail Z Q T Np
    ((Assembly.NII Z T : ℝ) + Dt) Df (tail.B T)
    htrace hfrob hB htr' hfr'
  refine ⟨?_, ?_⟩
  · simpa [currentAzTraceError, Q, Dt, add_assoc] using hcentral.trace_lower
  · have hsqrt : Real.sqrt (RHLinalg.frobSq (Q.hat T (Z.Gz Q T))) ≤
        Real.sqrt (kappa * Np + Df) := Real.sqrt_le_sqrt
          (hbase.trans (by
            simpa [add_comm] using (add_le_add_right
              (mul_le_mul_of_nonneg_left hNNp hk0) Df)))
    have hcross :
        Df + 2 * Real.sqrt (RHLinalg.frobSq (Q.hat T (Z.Gz Q T))) * tail.B T +
            tail.B T ^ 2 ≤
          currentAzFrobError Z P kappa tail T := by
      dsimp [currentAzFrobError, Df, Np]
      nlinarith [mul_le_mul_of_nonneg_right hsqrt hB]
    apply hcentral.frobenius_upper.trans
    linarith [hcross]

end Zeta23Ext.CurrentAzMoments
