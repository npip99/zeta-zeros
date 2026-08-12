/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentZetaNative

/-!
# The current-window autocorrelation estimate

This discharges the last analytic premise of the zeta-native moment route.
The proof compares the squared tapered window with the corresponding sharp
cutoff in `L¹`, then uses the standard two-term autocorrelation expansion.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Real Set MeasureTheory Filter Topology

namespace Zeta23Ext.CurrentZetaAutocorr

open Zeta23
open Zeta23.XiPrime
open Zeta23Ext.CurrentWindowMoments
open Zeta23Ext.CurrentZetaNative

/-- The sharp current profile at physical scale `L`. -/
def sharpCurrent (L : ℝ) (u : ℝ) : ℝ :=
  (Icc (-(L / 2)) (L / 2)).indicator
    (fun u => CurrentWindow.window (u / L)) u

private lemma scaled_mem_core {L u : ℝ} (hL : 0 < L)
    (hu : u ∈ Icc (-(L / 2)) (L / 2)) :
    u / L ∈ Icc (-(1 : ℝ) / 2) (1 / 2) := by
  constructor
  · rw [le_div_iff₀ hL]
    linarith [hu.1]
  · rw [div_le_iff₀ hL]
    linarith [hu.2]

/-- Exact autocorrelation of the sharp current profile. -/
theorem sharpCurrent_autocorr_eq (hL : 0 < L) {y : ℝ}
    (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    ∫ u, sharpCurrent L u * sharpCurrent L (u + y) =
      L * vConv CurrentWindow.window (y / L) := by
  have hind : ∀ u : ℝ, sharpCurrent L u * sharpCurrent L (u + y) =
      (Icc (-(L / 2)) (L / 2 - y)).indicator
        (fun u => CurrentWindow.window (u / L) *
          CurrentWindow.window ((u + y) / L)) u := by
    intro u
    unfold sharpCurrent
    by_cases hu : u ∈ Icc (-(L / 2)) (L / 2 - y)
    · have hu1 : u ∈ Icc (-(L / 2)) (L / 2) := ⟨hu.1, by linarith [hu.2]⟩
      have hu2 : u + y ∈ Icc (-(L / 2)) (L / 2) :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [indicator_of_mem hu, indicator_of_mem hu1, indicator_of_mem hu2]
    · rw [indicator_of_notMem hu]
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [indicator_of_notMem (s := Icc (-(L / 2)) (L / 2)) (a := u)
          (by rw [mem_Icc]; push Not; intro h; linarith), zero_mul]
      · rw [indicator_of_notMem (s := Icc (-(L / 2)) (L / 2)) (a := u + y)
          (by rw [mem_Icc]; push Not; intro h; linarith), mul_zero]
  rw [integral_congr_ae (ae_of_all _ hind), integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2 - y)]
  have hsub := intervalIntegral.integral_comp_div
    (a := -(L / 2)) (b := L / 2 - y)
    (f := fun s => CurrentWindow.window s *
      CurrentWindow.window (s + y / L)) hL.ne'
  have e1 : -(L / 2) / L = -(1 : ℝ) / 2 := by field_simp
  have e2 : (L / 2 - y) / L = 1 / 2 - y / L := by field_simp
  rw [e1, e2, smul_eq_mul] at hsub
  unfold vConv
  rw [← hsub]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [add_div]

/-- The squared tapered current window differs from its sharp counterpart by
at most `2w` in `L¹`. -/
theorem integral_abs_phiV_sq_sub_sharp {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {T : ℝ}
    (h2w : 2 * P.w ≤ P.L T) :
    ∫ u, |P.phiV CurrentWindow.window T u ^ 2 -
      sharpCurrent (P.L T) u| ≤ 2 * P.w := by
  let L := P.L T
  let w := P.w
  have hw : 0 < w := by dsimp [w]; linarith [hP.one_le_w]
  have hL : 0 < L := by dsimp [L, w] at h2w ⊢; linarith
  set maj : ℝ → ℝ := fun u =>
    (Icc (-(L / 2)) (-(L / 2) + w)).indicator (1 : ℝ → ℝ) u +
    (Icc (L / 2 - w) (L / 2)).indicator (1 : ℝ → ℝ) u with hmaj
  have hImaj : Integrable maj := by
    apply Integrable.add <;>
      exact (integrable_indicator_iff measurableSet_Icc).mpr
        (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hind0 : ∀ (s : Set ℝ) (u : ℝ),
      0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
    indicator_nonneg (fun _ _ => zero_le_one) u
  have hpt : ∀ u : ℝ,
      |P.phiV CurrentWindow.window T u ^ 2 - sharpCurrent L u| ≤ maj u := by
    intro u
    have hmaj0 : 0 ≤ maj u := by
      rw [hmaj]
      exact add_nonneg (hind0 _ u) (hind0 _ u)
    have hval : P.phiV CurrentWindow.window T u ^ 2 =
        clippedWindow (u / L) * Taper.phi P.ϱ L w u ^ 2 := by
      simpa [L, w] using phiV_sq_eq_clipped hP hcert hL
    rcases le_or_gt |u| (L / 2 - w) with hpl | hedge
    · have huIcc : u ∈ Icc (-(L / 2)) (L / 2) := by
        rw [abs_le] at hpl
        exact ⟨by linarith [hpl.1], by linarith [hpl.2]⟩
      have hscaled := scaled_mem_core hL huIcc
      rw [hval, Taper.phi_eq_one hP.taper hw hpl, one_pow, mul_one,
        clippedWindow_eq_on_core hcert hscaled]
      unfold sharpCurrent
      rw [indicator_of_mem huIcc, sub_self, abs_zero]
      exact hmaj0
    · rcases le_or_gt |u| (L / 2) with hin | hout
      · have huIcc : u ∈ Icc (-(L / 2)) (L / 2) :=
          abs_le.mp hin
        have hscaled := scaled_mem_core hL huIcc
        have hbound : |P.phiV CurrentWindow.window T u ^ 2 -
            sharpCurrent L u| ≤ 1 := by
          have h1 : 0 ≤ P.phiV CurrentWindow.window T u ^ 2 := sq_nonneg _
          have h2 : P.phiV CurrentWindow.window T u ^ 2 ≤ 1 := by
            rw [hval]
            calc
              clippedWindow (u / L) * Taper.phi P.ϱ L w u ^ 2 ≤ 1 * 1 := by
                apply mul_le_mul (clippedWindow_le_one _)
                  (by
                    calc Taper.phi P.ϱ L w u ^ 2 ≤ 1 ^ 2 :=
                        pow_le_pow_left₀ (Taper.phi_nonneg hP.taper u)
                          (Taper.phi_le_one hP.taper u) 2
                      _ = 1 := by norm_num)
                  (sq_nonneg _) zero_le_one
              _ = 1 := one_mul 1
          have h3 : 0 ≤ sharpCurrent L u := by
            unfold sharpCurrent
            rw [indicator_of_mem huIcc]
            exact CurrentWindow.window_nonneg_on_support hcert _ hscaled
          have h4 : sharpCurrent L u ≤ 1 := by
            unfold sharpCurrent
            rw [indicator_of_mem huIcc]
            exact hcert.upper _ hscaled
          rw [abs_le]
          constructor <;> linarith
        have hone : (1 : ℝ) ≤ maj u := by
          rw [hmaj]
          change (1 : ℝ) ≤
            (Icc (-(L / 2)) (-(L / 2) + w)).indicator (1 : ℝ → ℝ) u +
              (Icc (L / 2 - w) (L / 2)).indicator (1 : ℝ → ℝ) u
          rcases le_or_gt u 0 with hneg | hpos
          · have hu1 : u ∈ Icc (-(L / 2)) (-(L / 2) + w) := by
              have hau : |u| = -u := abs_of_nonpos hneg
              rw [hau] at hin hedge
              exact ⟨by linarith, by linarith⟩
            have hz := hind0 (Icc (L / 2 - w) (L / 2)) u
            rw [indicator_of_mem hu1, Pi.one_apply]
            linarith
          · have hu1 : u ∈ Icc (L / 2 - w) (L / 2) := by
              have hau : |u| = u := abs_of_pos hpos
              rw [hau] at hin hedge
              exact ⟨by linarith, by linarith⟩
            have hz := hind0 (Icc (-(L / 2)) (-(L / 2) + w)) u
            rw [indicator_of_mem hu1, Pi.one_apply]
            linarith
        exact hbound.trans hone
      · have hphi : Taper.phi P.ϱ L w u = 0 :=
          Taper.phi_eq_zero hP.taper hw (le_of_lt hout)
        have hsharp : sharpCurrent L u = 0 := by
          unfold sharpCurrent
          apply indicator_of_notMem
          intro hm
          have : |u| ≤ L / 2 := abs_le.mpr ⟨hm.1, hm.2⟩
          linarith
        rw [hval, hphi, zero_pow two_ne_zero, mul_zero, hsharp, sub_zero,
          abs_zero]
        exact hmaj0
  calc
    ∫ u, |P.phiV CurrentWindow.window T u ^ 2 - sharpCurrent L u|
        ≤ ∫ u, maj u := by
          apply integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _) hImaj
            (ae_of_all _ hpt)
    _ = 2 * w := by
      rw [hmaj, integral_add
        ((integrable_indicator_iff measurableSet_Icc).mpr
          (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
        ((integrable_indicator_iff measurableSet_Icc).mpr
          (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))),
        integral_indicator_one measurableSet_Icc,
        integral_indicator_one measurableSet_Icc, measureReal_def, measureReal_def,
        Real.volume_Icc, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
      ring
    _ = 2 * P.w := rfl

/-- Pointwise current-window autocorrelation comparison. -/
theorem autocorr_current_close_at {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {T y : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (hy : y ∈ Icc (0 : ℝ) (P.L T)) :
    |AdmWindow.gv (P.phiV CurrentWindow.window T) y -
      P.L T * vConv CurrentWindow.window (y / P.L T)| ≤ 4 * P.w := by
  let L := P.L T
  let h : ℝ → ℝ := fun u => P.phiV CurrentWindow.window T u ^ 2
  let k : ℝ → ℝ := sharpCurrent L
  have hW := CurrentWindowAdmissibility.admWindow_current hP hcert h8
  have hL : 0 < L := by dsimp [L]; linarith [hP.one_le_w]
  have hh_cont : Continuous h := hW.sq_continuous
  have hh1 : ∀ u, |h u| ≤ 1 := by
    intro u
    dsimp [h]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (hW.nonneg u) (hW.le_one u)
  have hk_meas : Measurable k := by
    dsimp [k, sharpCurrent]
    exact Measurable.indicator
      (CurrentWindow.continuous_window.comp (continuous_id.div_const L)).measurable
      measurableSet_Icc
  have hk1 : ∀ u, |k u| ≤ 1 := by
    intro u
    dsimp [k, sharpCurrent]
    by_cases hm : u ∈ Icc (-(L / 2)) (L / 2)
    · rw [indicator_of_mem hm, abs_le]
      have hs := scaled_mem_core hL hm
      exact ⟨by linarith [CurrentWindow.window_nonneg_on_support hcert _ hs],
        hcert.upper _ hs⟩
    · rw [indicator_of_notMem hm, abs_zero]
      exact zero_le_one
  have hint_h : Integrable h := hW.integrable_pow (by norm_num)
  have hint_k : Integrable k := by
    dsimp [k, sharpCurrent]
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (((CurrentWindow.continuous_window.comp
        (continuous_id.div_const L)).continuousOn).integrableOn_compact isCompact_Icc)
  have hint_d : Integrable (fun u => h u - k u) := hint_h.sub hint_k
  have hint_hy : Integrable (fun u => h (u + y)) := hint_h.comp_add_right y
  have hint_ky : Integrable (fun u => k (u + y)) := hint_k.comp_add_right y
  have hint_dy : Integrable (fun u => h (u + y) - k (u + y)) := hint_hy.sub hint_ky
  have hmeas_hy : AEStronglyMeasurable (fun u => h (u + y)) volume :=
    hint_hy.aestronglyMeasurable
  have hint_p1 : Integrable (fun u => (h u - k u) * h (u + y)) := by
    have ht := hint_d.bdd_mul (c := 1) hmeas_hy (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]; exact hh1 (u + y))
    exact ht.congr (ae_of_all _ fun u => by ring)
  have hint_p2 : Integrable (fun u => k u * (h (u + y) - k (u + y))) :=
    hint_dy.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]; exact hk1 u)
  have hint_hh : Integrable (fun u => h u * h (u + y)) := by
    have ht := hint_h.bdd_mul (c := 1) hmeas_hy (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]; exact hh1 (u + y))
    exact ht.congr (ae_of_all _ fun u => by ring)
  have hint_kk : Integrable (fun u => k u * k (u + y)) :=
    hint_ky.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]; exact hk1 u)
  have hCk : ∫ u, k u * k (u + y) =
      L * vConv CurrentWindow.window (y / L) :=
    sharpCurrent_autocorr_eq hL hy.1 hy.2
  have hdecomp : Params.autocorr h y -
      L * vConv CurrentWindow.window (y / L) =
      (∫ u, (h u - k u) * h (u + y)) +
        ∫ u, k u * (h (u + y) - k (u + y)) := by
    have e1 : Params.autocorr h y - L * vConv CurrentWindow.window (y / L) =
        ∫ u, (h u * h (u + y) - k u * k (u + y)) := by
      rw [show Params.autocorr h y = ∫ u, h u * h (u + y) from rfl,
        ← hCk, integral_sub hint_hh hint_kk]
    rw [e1, ← integral_add hint_p1 hint_p2]
    exact integral_congr_ae (ae_of_all _ fun u => by ring)
  have hd2w : ∫ u, |h u - k u| ≤ 2 * P.w := by
    simpa [h, k, L] using integral_abs_phiV_sq_sub_sharp hP hcert
      (by linarith : 2 * P.w ≤ P.L T)
  have hint_dabs : Integrable (fun u => |h u - k u|) := hint_d.abs
  have hb1 : |∫ u, (h u - k u) * h (u + y)| ≤ 2 * P.w := by
    calc
      |∫ u, (h u - k u) * h (u + y)|
          ≤ ∫ u, |(h u - k u) * h (u + y)| := abs_integral_le_integral_abs
      _ ≤ ∫ u, |h u - k u| := by
        apply integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _) hint_dabs
        refine ae_of_all _ fun u => ?_
        change |(h u - k u) * h (u + y)| ≤ |h u - k u|
        rw [abs_mul]
        simpa using mul_le_mul_of_nonneg_left (hh1 (u + y)) (abs_nonneg (h u - k u))
      _ ≤ 2 * P.w := hd2w
  have hb2 : |∫ u, k u * (h (u + y) - k (u + y))| ≤ 2 * P.w := by
    have htrans : ∫ u, |h (u + y) - k (u + y)| =
        ∫ u, |h u - k u| := integral_add_right_eq_self (fun u => |h u - k u|) y
    calc
      |∫ u, k u * (h (u + y) - k (u + y))|
          ≤ ∫ u, |k u * (h (u + y) - k (u + y))| := abs_integral_le_integral_abs
      _ ≤ ∫ u, |h (u + y) - k (u + y)| := by
        apply integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _) hint_dy.abs
        refine ae_of_all _ fun u => ?_
        change |k u * (h (u + y) - k (u + y))| ≤
          |h (u + y) - k (u + y)|
        rw [abs_mul]
        simpa using mul_le_mul_of_nonneg_right (hk1 u)
          (abs_nonneg (h (u + y) - k (u + y)))
      _ = ∫ u, |h u - k u| := htrans
      _ ≤ 2 * P.w := hd2w
  change |Params.autocorr h y - L * vConv CurrentWindow.window (y / L)| ≤ 4 * P.w
  rw [hdecomp]
  exact (abs_add_le _ _).trans (by linarith)

/-- The current autocorrelation premise is unconditional from admissibility. -/
theorem currentAutocorr (P : Params) (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) : CurrentAutocorr P := by
  filter_upwards [Params.eventually_w8 hP] with T h8
  intro y hy
  exact autocorr_current_close_at hP hcert h8 hy

/-- Zeta zero-side moments with no remaining autocorrelation premise. -/
theorem current_zeta_gzMoments {P : Params}
    (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate) :
    GzMoments zetaZeroConfig (P.atV CurrentWindow.window)
      (cWin id P.lam CurrentWindow.window)⁻¹ :=
  current_zeta_gzMoments_of_autocorr hP hlam hcert
    (currentAutocorr P hP hcert)

end Zeta23Ext.CurrentZetaAutocorr
