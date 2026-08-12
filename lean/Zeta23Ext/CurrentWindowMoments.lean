/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowAdmissibility
import Zeta23.XiPrime.Window.Quartic
import Zeta23.XiPrime.PrimeSide.Traces

/-!
# The first two asymptotic moments of the current window

The current cosine polynomial is certified only on the unit core.  To apply
the upstream edge estimate without asserting a false global bound, we clamp
it outside that core.  The clamp agrees with the original profile wherever
the taper can be nonzero, so it computes the actual `P.phiV` moments.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Zeta23Ext.CurrentWindowMoments

open Zeta23
open Zeta23.XiPrime

/-- A globally bounded continuous extension used only in the edge estimate. -/
def clippedWindow (s : ℝ) : ℝ := min 1 (max 0 (CurrentWindow.window s))

lemma clippedWindow_nonneg (s : ℝ) : 0 ≤ clippedWindow s := by
  unfold clippedWindow
  exact le_min zero_le_one (le_max_left _ _)

lemma clippedWindow_le_one (s : ℝ) : clippedWindow s ≤ 1 := min_le_left _ _

lemma abs_clippedWindow_le_one (s : ℝ) : |clippedWindow s| ≤ 1 := by
  rw [abs_of_nonneg (clippedWindow_nonneg s)]
  exact clippedWindow_le_one s

lemma continuous_clippedWindow : Continuous clippedWindow := by
  unfold clippedWindow
  exact continuous_const.min (continuous_const.max CurrentWindow.continuous_window)

lemma clippedWindow_eq_on_core (hcert : CurrentWindow.WindowCertificate)
    {s : ℝ} (hs : s ∈ Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) :
    clippedWindow s = CurrentWindow.window s := by
  unfold clippedWindow
  have h0 : 0 ≤ CurrentWindow.window s :=
    CurrentWindow.window_nonneg_on_support hcert s hs
  rw [max_eq_right h0, min_eq_right (hcert.upper s hs)]

/-- The certified lower bound makes the square mass strictly positive. -/
lemma current_window_sq_integral_pos
    (hcert : CurrentWindow.WindowCertificate) :
    0 < ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
      CurrentWindow.window s ^ 2 := by
  have hint : IntervalIntegrable (fun s => CurrentWindow.window s ^ 2)
      volume (-(1 : ℝ) / 2) ((1 : ℝ) / 2) :=
    (CurrentWindow.continuous_window.pow 2).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (a := -(1 : ℝ) / 2)
    (b := (1 : ℝ) / 2) (f := fun _ => (9 : ℝ) / 16)
    (g := fun s => CurrentWindow.window s ^ 2) (by norm_num)
    intervalIntegrable_const hint
    (fun s hs => by nlinarith [hcert.lower s hs])
  refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < 9 / 16) ?_
  calc
    (9 : ℝ) / 16 =
        ∫ _s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), (9 : ℝ) / 16 := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          norm_num
    _ ≤ ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
        CurrentWindow.window s ^ 2 := hmono

private lemma scaled_mem_core {L u : ℝ} (hL : 0 < L) (hu : |u| ≤ L / 2) :
    u / L ∈ Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
  rw [mem_Icc]
  obtain ⟨hu₁, hu₂⟩ := abs_le.mp hu
  constructor
  · rw [le_div_iff₀ hL]
    linarith
  · rw [div_le_iff₀ hL]
    linarith

lemma phiV_sq_eq_clipped {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {T u : ℝ} (hL : 0 < P.L T) :
    P.phiV CurrentWindow.window T u ^ 2 =
      clippedWindow (u / P.L T) * Taper.phi P.ϱ (P.L T) P.w u ^ 2 := by
  rw [Params.phiV_eq, mul_pow, Real.sq_sqrt (le_max_left _ _)]
  by_cases hu : |u| ≤ P.L T / 2
  · have hs := scaled_mem_core hL hu
    rw [clippedWindow_eq_on_core hcert hs,
      max_eq_right (CurrentWindow.window_nonneg_on_support hcert _ hs)]
  · have hz := Taper.phi_eq_zero (L := P.L T) (w := P.w) hP.taper
      (by linarith [hP.one_le_w])
      (le_of_not_ge hu)
    rw [hz, zero_pow two_ne_zero, mul_zero, mul_zero]

lemma phiV_fourth_eq_clipped_sq {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {T u : ℝ} (hL : 0 < P.L T) :
    P.phiV CurrentWindow.window T u ^ 4 =
      clippedWindow (u / P.L T) ^ 2 * Taper.phi P.ϱ (P.L T) P.w u ^ 4 := by
  rw [show P.phiV CurrentWindow.window T u ^ 4 =
      (P.phiV CurrentWindow.window T u ^ 2) ^ 2 by ring,
    phiV_sq_eq_clipped hP hcert hL]
  ring

theorem aV_current_close {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) :
    |AdmWindow.av (P.phiV CurrentWindow.window T) (P.L T) -
      CurrentWindow.windowMass CurrentWindow.window| ≤ 2 * P.w / P.L T := by
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have h2w : 2 * P.w ≤ P.L T := by linarith
  have hL : 0 < P.L T := by linarith
  have hsub : CurrentWindow.windowMass CurrentWindow.window =
      (P.L T)⁻¹ * ∫ u in Icc (-(P.L T / 2)) (P.L T / 2),
        clippedWindow (u / P.L T) := by
    rw [setIntegral_congr_fun measurableSet_Icc
      (fun u hu => clippedWindow_eq_on_core hcert (scaled_mem_core hL
        (abs_le.mpr ⟨hu.1, hu.2⟩))),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(P.L T / 2) ≤ P.L T / 2),
      XiPrime.integral_scale hL]
    unfold CurrentWindow.windowMass
    field_simp
  have hwin : ∫ u, P.phiV CurrentWindow.window T u ^ 2 =
      ∫ u, clippedWindow (u / P.L T) *
        Taper.phi P.ϱ (P.L T) P.w u ^ 2 :=
    integral_congr_ae (ae_of_all _ fun u => phiV_sq_eq_clipped hP hcert hL)
  rw [AdmWindow.av, hwin, hsub]
  have hedge := XiPrime.edge_estimate
    (h := fun u => clippedWindow (u / P.L T))
    (p := fun u => Taper.phi P.ϱ (P.L T) P.w u ^ 2)
    hL hw0 h2w
    (fun u => abs_clippedWindow_le_one _)
    (fun u => sq_nonneg _)
    (fun u => by
      calc Taper.phi P.ϱ (P.L T) P.w u ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (Taper.phi_nonneg hP.taper u)
            (Taper.phi_le_one hP.taper u) 2
        _ = 1 := one_pow 2)
    (fun u hu => by rw [Taper.phi_eq_one hP.taper hw0 hu, one_pow])
    (fun u hu => by rw [Taper.phi_eq_zero hP.taper hw0 hu, zero_pow two_ne_zero])
    ((Taper.phi_continuous hP.taper hw0 h2w).pow 2)
    (continuous_clippedWindow.comp (continuous_id.div_const _))
  have heq : (P.L T)⁻¹ *
        (∫ u, clippedWindow (u / P.L T) * Taper.phi P.ϱ (P.L T) P.w u ^ 2) -
      (P.L T)⁻¹ * ∫ u in Icc (-(P.L T / 2)) (P.L T / 2),
        clippedWindow (u / P.L T) =
      (P.L T)⁻¹ * ((∫ u, clippedWindow (u / P.L T) *
        Taper.phi P.ϱ (P.L T) P.w u ^ 2) -
          ∫ u in Icc (-(P.L T / 2)) (P.L T / 2),
            clippedWindow (u / P.L T)) := by ring
  rw [heq, abs_mul, abs_of_pos (by positivity : 0 < (P.L T)⁻¹)]
  calc
    (P.L T)⁻¹ * |(∫ u, clippedWindow (u / P.L T) *
          Taper.phi P.ϱ (P.L T) P.w u ^ 2) -
        ∫ u in Icc (-(P.L T / 2)) (P.L T / 2),
          clippedWindow (u / P.L T)|
      ≤ (P.L T)⁻¹ * (2 * P.w) :=
        mul_le_mul_of_nonneg_left hedge (by positivity)
    _ = 2 * P.w / P.L T := by rw [div_eq_inv_mul]

theorem bV_current_close {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) :
    |AdmWindow.bv (P.phiV CurrentWindow.window T) (P.L T) -
      CurrentWindow.windowSquareMass CurrentWindow.window| ≤ 2 * P.w / P.L T := by
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have h2w : 2 * P.w ≤ P.L T := by linarith
  have hL : 0 < P.L T := by linarith
  have hsub : CurrentWindow.windowSquareMass CurrentWindow.window =
      (P.L T)⁻¹ * ∫ u in Icc (-(P.L T / 2)) (P.L T / 2),
        clippedWindow (u / P.L T) ^ 2 := by
    rw [setIntegral_congr_fun measurableSet_Icc
      (fun u hu => by rw [clippedWindow_eq_on_core hcert (scaled_mem_core hL
        (abs_le.mpr ⟨hu.1, hu.2⟩))]),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(P.L T / 2) ≤ P.L T / 2),
      XiPrime.integral_scale (g := fun s => CurrentWindow.window s ^ 2) hL]
    unfold CurrentWindow.windowSquareMass
    field_simp
  have hwin : ∫ u, P.phiV CurrentWindow.window T u ^ 4 =
      ∫ u, clippedWindow (u / P.L T) ^ 2 *
        Taper.phi P.ϱ (P.L T) P.w u ^ 4 :=
    integral_congr_ae (ae_of_all _ fun u => phiV_fourth_eq_clipped_sq hP hcert hL)
  rw [AdmWindow.bv, hwin, hsub]
  have hedge := XiPrime.edge_estimate
    (h := fun u => clippedWindow (u / P.L T) ^ 2)
    (p := fun u => Taper.phi P.ϱ (P.L T) P.w u ^ 4)
    hL hw0 h2w
    (fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [clippedWindow_nonneg (u / P.L T), clippedWindow_le_one (u / P.L T)])
    (fun u => by positivity)
    (fun u => by
      calc Taper.phi P.ϱ (P.L T) P.w u ^ 4 ≤ 1 ^ 4 :=
          pow_le_pow_left₀ (Taper.phi_nonneg hP.taper u)
            (Taper.phi_le_one hP.taper u) 4
        _ = 1 := one_pow 4)
    (fun u hu => by rw [Taper.phi_eq_one hP.taper hw0 hu, one_pow])
    (fun u hu => by rw [Taper.phi_eq_zero hP.taper hw0 hu]; norm_num)
    ((Taper.phi_continuous hP.taper hw0 h2w).pow 4)
    ((continuous_clippedWindow.comp (continuous_id.div_const _)).pow 2)
  have heq : (P.L T)⁻¹ *
        (∫ u, clippedWindow (u / P.L T) ^ 2 * Taper.phi P.ϱ (P.L T) P.w u ^ 4) -
      (P.L T)⁻¹ * ∫ u in Icc (-(P.L T / 2)) (P.L T / 2),
        clippedWindow (u / P.L T) ^ 2 =
      (P.L T)⁻¹ * ((∫ u, clippedWindow (u / P.L T) ^ 2 *
        Taper.phi P.ϱ (P.L T) P.w u ^ 4) -
          ∫ u in Icc (-(P.L T / 2)) (P.L T / 2),
            clippedWindow (u / P.L T) ^ 2) := by ring
  rw [heq, abs_mul, abs_of_pos (by positivity : 0 < (P.L T)⁻¹)]
  calc
    (P.L T)⁻¹ * |(∫ u, clippedWindow (u / P.L T) ^ 2 *
          Taper.phi P.ϱ (P.L T) P.w u ^ 4) -
        ∫ u in Icc (-(P.L T / 2)) (P.L T / 2),
          clippedWindow (u / P.L T) ^ 2|
      ≤ (P.L T)⁻¹ * (2 * P.w) :=
        mul_le_mul_of_nonneg_left hedge (by positivity)
    _ = 2 * P.w / P.L T := by rw [div_eq_inv_mul]

theorem tendsto_aV_current {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    Tendsto (fun T => AdmWindow.av (P.phiV CurrentWindow.window T) (P.L T))
      atTop (𝓝 (CurrentWindow.windowMass CurrentWindow.window)) := by
  apply ThmD.tendsto_of_close hP.lam_pos
  filter_upwards [Params.eventually_w8 hP] with T hT
  exact aV_current_close hP hcert hT

theorem tendsto_bV_current {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    Tendsto (fun T => AdmWindow.bv (P.phiV CurrentWindow.window T) (P.L T))
      atTop (𝓝 (CurrentWindow.windowSquareMass CurrentWindow.window)) := by
  apply ThmD.tendsto_of_close hP.lam_pos
  filter_upwards [Params.eventually_w8 hP] with T hT
  exact bV_current_close hP hcert hT

/-- The generic upstream ratio theorem specialized using the proved current
first and second moments.  Only the actual autocorrelation comparison remains
as a window-specific asymptotic premise. -/
theorem tendsto_cRatio_current_of_autocorr {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {D : ℝ → ℝ}
    (hD : ContinuousOn D (Icc 0 1))
    (hD0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ D x)
    (hg : ∀ᶠ T in atTop, ∀ y ∈ Icc (0 : ℝ) (P.L T),
      |AdmWindow.gv (P.phiV CurrentWindow.window T) y -
        P.L T * vConv CurrentWindow.window (y / P.L T)| ≤ 4 * P.w) :
    Tendsto (fun T => ThmD.cRatio (P.lam1 T)
      (AdmWindow.av (P.phiV CurrentWindow.window T) (P.L T))
      (AdmWindow.bv (P.phiV CurrentWindow.window T) (P.L T))
      (JD D (AdmWindow.gv (P.phiV CurrentWindow.window T))
        (P.L T) (Zeta23.l T))) atTop
      (𝓝 (cWin D P.lam CurrentWindow.window)) := by
  have hgc : ∀ᶠ T in atTop,
      Continuous (AdmWindow.gv (P.phiV CurrentWindow.window T)) := by
    filter_upwards [Params.eventually_w8 hP] with T h8
    exact (CurrentWindowAdmissibility.admWindow_current hP hcert h8).gv_continuous
  have hJ := tendsto_JT_of_autocorr_close (v := CurrentWindow.window)
    hP hD CurrentWindow.continuous_window hgc hg
  refine tendsto_cRatio_cWin hP.lam_pos (ThmD.tendsto_lam1 hP.lam_pos)
    (tendsto_aV_current hP hcert) (tendsto_bV_current hP hcert) hJ ?_
  exact cWin_denom_pos (current_window_sq_integral_pos hcert)
    (jWin_nonneg hD0 (CurrentWindow.window_nonneg_on_support hcert)
      hP.lam_pos.le hP.lam_le_one) hP.lam_pos.le

end Zeta23Ext.CurrentWindowMoments
