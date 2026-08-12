/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentZetaAutocorr

/-!
# The current zeta endpoint and a fixed subunit scale

This identifies the autocorrelation form used by `XiPrime.cWin id 1` with
the symmetric distance form used by the current-window `H` certificate.
Continuity then moves the strict endpoint inequality to a fixed `lam < 1`.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Real Set MeasureTheory Filter Topology

namespace Zeta23Ext.CurrentZetaEndpoint

open Zeta23
open Zeta23.XiPrime
open Zeta23Ext.CurrentWindow

private theorem triangle_swap {a b : ℝ} (hab : a ≤ b) {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) :
    (∫ s in a..b, ∫ r in 0..b - s, F s r) =
      ∫ r in 0..b - a, ∫ s in a..b - r, F s r := by
  let S : Set (ℝ × ℝ) := {p | p.2 ≤ b - p.1}
  let q : ℝ → ℝ → ℝ := fun s r =>
    S.indicator (Function.uncurry F) (s, r)
  have hS : MeasurableSet S := by
    exact (isClosed_le continuous_snd (continuous_const.sub continuous_fst)).measurableSet
  have hq : IntegrableOn (Function.uncurry q)
      (uIoc a b ×ˢ uIoc (0 : ℝ) (b - a)) := by
    have hbase : IntegrableOn (Function.uncurry F)
        (uIcc a b ×ˢ uIcc (0 : ℝ) (b - a)) :=
      hF.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
    have hind : IntegrableOn (S.indicator (Function.uncurry F))
        (uIcc a b ×ˢ uIcc (0 : ℝ) (b - a)) := hbase.indicator hS
    exact hind.mono_set (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hs (s : ℝ) (hs : s ∈ uIcc a b) :
      (∫ r in (0 : ℝ)..b - a, q s r) = ∫ r in 0..b - s, F s r := by
    rw [uIcc_of_le hab] at hs
    have hsa : a ≤ s := hs.1
    have hsb : s ≤ b := hs.2
    have hm : b - s ∈ Icc (0 : ℝ) (b - a) := ⟨by linarith, by linarith⟩
    rw [← intervalIntegral.integral_indicator (f := fun r => F s r) hm]
    apply intervalIntegral.integral_congr
    intro r _
    simp only [q, S, Function.uncurry_apply_pair]
    rfl
  have hr (r : ℝ) (hr : r ∈ uIcc (0 : ℝ) (b - a)) :
      (∫ s in a..b, q s r) = ∫ s in a..b - r, F s r := by
    rw [uIcc_of_le (sub_nonneg.mpr hab)] at hr
    have hr0 : 0 ≤ r := hr.1
    have hrB : r ≤ b - a := hr.2
    have hm : b - r ∈ Icc a b := ⟨by linarith, by linarith⟩
    rw [← intervalIntegral.integral_indicator (f := fun s => F s r) hm]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [q, S, Function.uncurry_apply_pair]
    by_cases h : r ≤ b - s
    · have h' : s ≤ b - r := by linarith
      rw [indicator_of_mem (show (s, r) ∈ {p : ℝ × ℝ | p.2 ≤ b - p.1} from h),
        indicator_of_mem (show s ∈ {x : ℝ | x ≤ b - r} from h')]
      rfl
    · have h' : ¬s ≤ b - r := by linarith
      rw [indicator_of_notMem
          (show (s, r) ∉ {p : ℝ × ℝ | p.2 ≤ b - p.1} from h),
        indicator_of_notMem (show s ∉ {x : ℝ | x ≤ b - r} from h')]
  calc
    (∫ s in a..b, ∫ r in 0..b - s, F s r) =
        ∫ s in a..b, ∫ r in 0..b - a, q s r := by
          apply intervalIntegral.integral_congr
          intro s hs'
          exact (hs s hs').symm
    _ = ∫ r in 0..b - a, ∫ s in a..b, q s r :=
      intervalIntegral_intervalIntegral_swap hq
    _ = ∫ r in 0..b - a, ∫ s in a..b - r, F s r := by
      apply intervalIntegral.integral_congr
      intro r hr'
      exact hr r hr'

/-- On a symmetric unit interval, the double distance integral is the
one-sided autocorrelation integral.  The evenness hypothesis is used only to
identify the two triangular halves of the square. -/
theorem distanceMass_eq_two_integral_vConv {v : ℝ → ℝ}
    (hv : Continuous v) (heven : ∀ s : ℝ, v (-s) = v s) :
    CurrentWindow.windowDistanceMass v =
      2 * ∫ r in (0 : ℝ)..1, r * vConv v r := by
  let a : ℝ := -(1 : ℝ) / 2
  let b : ℝ := (1 : ℝ) / 2
  let lower : ℝ → ℝ := fun s =>
    ∫ t in a..s, (s - t) * v s * v t
  let upper : ℝ → ℝ := fun s =>
    ∫ t in s..b, (t - s) * v s * v t
  have hab : a ≤ b := by dsimp [a, b]; norm_num
  have hsplit (s : ℝ) (hs : s ∈ Icc a b) :
      (∫ t in a..b, |s - t| * v s * v t) = lower s + upper s := by
    have hcont : Continuous (fun t : ℝ => |s - t| * v s * v t) := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    apply congrArg₂ (· + ·)
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs.1] at ht
      dsimp [lower]
      rw [abs_of_nonneg (by linarith [ht.2])]
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs.2] at ht
      dsimp [upper]
      rw [abs_of_nonpos (by linarith [ht.1])]
      ring
  have hlower_point (s : ℝ) : lower (-s) = upper s := by
    have hneg := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => ((-s) + u) * v (-s) * v (-u))
      (a := a) (b := -s)
    have ha : -a = b := by dsimp [a, b]; ring
    rw [ha] at hneg
    calc
      lower (-s) = ∫ t in a..-s,
          ((-s) + (-t)) * v (-s) * v (-(-t)) := by
            apply intervalIntegral.integral_congr
            intro t _
            dsimp [lower]
            ring_nf
      _ = ∫ u in s..b, ((-s) + u) * v (-s) * v (-u) := by
        convert hneg using 1 <;> ring
      _ = upper s := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp [upper]
        rw [heven s, heven u]
        ring
  have hlower_eq_upper :
      (∫ s in a..b, lower s) = ∫ s in a..b, upper s := by
    have hneg := intervalIntegral.integral_comp_neg (f := lower) (a := a) (b := b)
    have hba : -b = a := by dsimp [a, b]; ring
    have hab' : -a = b := by dsimp [a, b]; ring
    rw [hba, hab'] at hneg
    calc
      (∫ s in a..b, lower s) = ∫ s in a..b, lower (-s) := hneg.symm
      _ = ∫ s in a..b, upper s := by
        apply intervalIntegral.integral_congr
        intro s _
        exact hlower_point s
  have hupper_inner (s : ℝ) : upper s =
      ∫ r in (0 : ℝ)..b - s, r * v s * v (s + r) := by
    have hshift := intervalIntegral.integral_comp_add_right
      (f := fun t : ℝ => (t - s) * v s * v t) (a := 0) (b := b - s) s
    calc
      upper s = ∫ t in s..b, (t - s) * v s * v t := rfl
      _ = ∫ r in (0 : ℝ)..b - s, ((r + s) - s) * v s * v (r + s) := by
        convert hshift.symm using 1 <;> ring
      _ = ∫ r in (0 : ℝ)..b - s, r * v s * v (s + r) := by
        apply intervalIntegral.integral_congr
        intro r _
        ring_nf
  have hF : Continuous (Function.uncurry
      (fun s r : ℝ => r * v s * v (s + r))) := by
    fun_prop
  have htri := triangle_swap hab hF
  have hba_one : b - a = 1 := by dsimp [a, b]; norm_num
  have hupper_conv : (∫ s in a..b, upper s) =
      ∫ r in (0 : ℝ)..1, r * vConv v r := by
    calc
      (∫ s in a..b, upper s) =
          ∫ s in a..b, ∫ r in (0 : ℝ)..b - s, r * v s * v (s + r) := by
            apply intervalIntegral.integral_congr
            intro s _
            exact hupper_inner s
      _ = ∫ r in (0 : ℝ)..b - a,
          ∫ s in a..b - r, r * v s * v (s + r) := htri
      _ = ∫ r in (0 : ℝ)..1, r * vConv v r := by
        rw [hba_one]
        apply intervalIntegral.integral_congr
        intro r _
        unfold vConv
        change (∫ s in a..b - r, r * v s * v (s + r)) =
          r * ∫ s in a..b - r, v s * v (s + r)
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro s _
        ring
  unfold CurrentWindow.windowDistanceMass
  change (∫ s in a..b, ∫ t in a..b, |s - t| * v s * v t) = _
  calc
    (∫ s in a..b, ∫ t in a..b, |s - t| * v s * v t) =
        ∫ s in a..b, (lower s + upper s) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hab] at hs
          exact hsplit s hs
    _ = (∫ s in a..b, lower s) + ∫ s in a..b, upper s := by
      rw [intervalIntegral.integral_add]
      · exact (show Continuous lower by
          dsimp [lower]
          exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
            (by fun_prop) continuous_id).intervalIntegrable _ _
      · exact (show Continuous upper by
          dsimp [upper]
          have hc : Continuous (fun s : ℝ =>
              ∫ t in b..s, (t - s) * v s * v t) :=
            intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
              (by fun_prop) continuous_id
          have heq : (fun s : ℝ => ∫ t in s..b, (t - s) * v s * v t) =
              fun s : ℝ => -(∫ t in b..s, (t - s) * v s * v t) := by
            funext s
            exact intervalIntegral.integral_symm b s
          rw [heq]
          exact hc.neg).intervalIntegrable _ _
    _ = 2 * ∫ r in (0 : ℝ)..1, r * vConv v r := by
      rw [hlower_eq_upper, hupper_conv]
      ring

/-- Autocorrelation and distance forms agree for the current cosine window. -/
theorem current_distanceMass_eq_two_integral_vConv :
    CurrentWindow.windowDistanceMass CurrentWindow.window =
      2 * ∫ r in (0 : ℝ)..1, r * vConv CurrentWindow.window r :=
  distanceMass_eq_two_integral_vConv CurrentWindow.continuous_window
    CurrentWindow.window_even

/-- At `lam = 1`, the zeta-native `cWin` is exactly the endpoint functional
used by the finite current-window certificate. -/
theorem current_cWin_one_eq_c1 :
    cWin id 1 CurrentWindow.window = CurrentWindow.c1 CurrentWindow.window := by
  unfold cWin jWin CurrentWindow.c1 CurrentWindow.windowMass
    CurrentWindow.windowSquareMass
  rw [current_distanceMass_eq_two_integral_vConv]
  simp only [id_eq, one_mul]

/-- Any strict certified endpoint inequality persists at one fixed scale
strictly below one. -/
theorem exists_current_lambda_of_Hcert_lt
    (hcert : CurrentWindow.WindowCertificate)
    (hstrict : CurrentWindow.Hcert < CurrentWindow.H CurrentWindow.window) :
    ∃ lam : ℝ, 1 / 2 ≤ lam ∧ lam < 1 ∧
      (cWin id lam CurrentWindow.window)⁻¹ < 2 - CurrentWindow.Hcert := by
  have hmass : (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
      CurrentWindow.window s) ≠ 0 := by
    have hp : 0 < CurrentWindow.windowMass CurrentWindow.window := by
      rw [← CurrentWindow.kernel_zero_eq_mass]
      exact CurrentWindow.kernel_zero_pos hcert
    exact ne_of_gt hp
  have hsq : 0 < ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
      CurrentWindow.window s ^ 2 :=
    CurrentWindowMoments.current_window_sq_integral_pos hcert
  have hc : ContinuousOn
      (fun lam => 1 / cWin id lam CurrentWindow.window) (Ioc (0 : ℝ) 1) :=
    continuousOn_inv_cWin continuous_id (fun _ hx => hx.1)
      CurrentWindow.continuous_window
      (CurrentWindow.window_nonneg_on_support hcert) hmass hsq
  have hsub : Icc (1 / 2 : ℝ) 1 ⊆ Ioc (0 : ℝ) 1 := by
    intro lam hlam
    exact ⟨by linarith [hlam.1], hlam.2⟩
  let f : ℝ → ℝ := fun lam =>
    (2 - CurrentWindow.Hcert) - 1 / cWin id lam CurrentWindow.window
  have hf : ContinuousOn f (Icc (1 / 2 : ℝ) 1) :=
    continuousOn_const.sub (hc.mono hsub)
  have hf1 : 0 < f 1 := by
    dsimp [f]
    rw [current_cWin_one_eq_c1]
    unfold CurrentWindow.H at hstrict
    linarith
  obtain ⟨lam, hlam0, hlam1, hlam⟩ := exists_lt_one_pos hf hf1
  refine ⟨lam, hlam0, hlam1, ?_⟩
  have hlt : 1 / cWin id lam CurrentWindow.window < 2 - CurrentWindow.Hcert := by
    dsimp [f] at hlam
    linarith
  simpa only [one_div] using hlt

/-- The preceding scale can be installed in the standard taper parameters
used by the zeta-native moment and zero-side theorems. -/
theorem exists_current_params_of_Hcert_lt
    (hcert : CurrentWindow.WindowCertificate)
    (hstrict : CurrentWindow.Hcert < CurrentWindow.H CurrentWindow.window) :
    ∃ P : Params, P.Valid ∧ 1 / 2 ≤ P.lam ∧ P.lam < 1 ∧
      (cWin id P.lam CurrentWindow.window)⁻¹ < 2 - CurrentWindow.Hcert := by
  obtain ⟨lam, hlam0, hlam1, hbound⟩ :=
    exists_current_lambda_of_Hcert_lt hcert hstrict
  let P : Params := paramsOf stdProfile lam
  have hP : P.Valid := by
    apply paramsOf_valid taperProfile_stdProfile
    · linarith [hlam0]
    · exact hlam1.le
  have hPlam : P.lam = lam := rfl
  exact ⟨P, hP, hPlam.symm ▸ hlam0, hPlam.symm ▸ hlam1,
    hPlam.symm ▸ hbound⟩

/-- Fixed standard parameters simultaneously carrying the unconditional zeta
zero-side moment theorem and the certified strict scalar bound. -/
theorem exists_current_zeta_moment_params_of_Hcert_lt
    (hcert : CurrentWindow.WindowCertificate)
    (hstrict : CurrentWindow.Hcert < CurrentWindow.H CurrentWindow.window) :
    ∃ P : Params, P.Valid ∧ 1 / 2 ≤ P.lam ∧ P.lam < 1 ∧
      GzMoments zetaZeroConfig (P.atV CurrentWindow.window)
        (cWin id P.lam CurrentWindow.window)⁻¹ ∧
      (cWin id P.lam CurrentWindow.window)⁻¹ < 2 - CurrentWindow.Hcert := by
  obtain ⟨P, hP, hlam0, hlam1, hbound⟩ :=
    exists_current_params_of_Hcert_lt hcert hstrict
  exact ⟨P, hP, hlam0, hlam1,
    CurrentZetaAutocorr.current_zeta_gzMoments hP hlam1 hcert, hbound⟩

end Zeta23Ext.CurrentZetaEndpoint
