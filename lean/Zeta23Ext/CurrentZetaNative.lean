/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentAnalyticInstantiation
import Zeta23Ext.CurrentWindowMoments
import Zeta23.XiPrime.ExplicitFormula.PrimeTermJ
import Zeta23.Final

/-!
# The zeta-native analytic route for the current window

This module records the feasibility gate for connecting the current cosine
window to the zeros of the Riemann zeta function.  It deliberately does not
pass through `xiDerivZeros₀`, `D1`, `XiEF`, or coefficient re-expansion.

The coefficient family is the zeta family `c_N = -Λ(N)`, with diagonal
density `D(s) = s`.  For this family the generic fixed-coefficient matrix
`GpC` is definitionally the ordinary zeta prime-side matrix `Gp`, after the
proved identity `Pc(-Λ) = PX`.  Weil's explicit formula then identifies
`Gp` with the actual zeta zero-side matrix at each sufficiently large height.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Filter Matrix MeasureTheory Set Topology
open scoped BigOperators ArithmeticFunction

namespace Zeta23Ext.CurrentZetaNative

open Zeta23
open Zeta23.XiPrime
open Zeta23Ext.CurrentAnalyticInstantiation

/-- The coefficient family native to the Riemann zeta explicit formula. -/
def zetaCoeffFamily : CoeffFamily where
  c := fun _ N => -((Λ N : ℝ) : ℂ)
  D := fun s => s

@[simp] lemma zetaCoeffFamily_c (T : ℝ) (N : ℕ) :
    zetaCoeffFamily.c T N = -((Λ N : ℝ) : ℂ) := rfl

@[simp] lemma zetaCoeffFamily_D (s : ℝ) : zetaCoeffFamily.D s = s := rfl

/-- The only genuinely asymptotic coefficient-family field, isolated from
the elementary upper bounds.  Its content is the uniform form of
`sum_{ℕ≤exp y} Λ(ℕ)^2/ℕ = y^2/2 + O(y)`. -/
def ZetaCoeffH3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ y : ℝ,
    0 ≤ y → y ≤ l T →
    |(∑ N ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
        ‖zetaCoeffFamily.c T N‖ ^ 2 / N) -
        l T ^ 2 * ∫ s in (0 : ℝ)..(y / l T), zetaCoeffFamily.D s|
      ≤ ε * l T ^ 2

/-- All fields of the zeta coefficient hypotheses except the classical
uniform diagonal asymptotic are discharged here. -/
theorem zetaCoeffFamily_hyps_of_H3 (hH3 : ZetaCoeffH3) :
    zetaCoeffFamily.Hyps where
  c_one := by
    intro T
    simp [zetaCoeffFamily, ArithmeticFunction.vonMangoldt_apply_one]
  H1 := by
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (PaperParams.eventually_l_ge 1)
    refine ⟨2 * Real.log 4 + 16, T₀, ?_⟩
    intro T hT x hx _hxupper
    have hl : 1 ≤ l T := hT₀ T hT
    have hsum := Cheb.sum_vonMangoldt_div_sqrt_le (x := x) (by linarith)
    simp only [zetaCoeffFamily_c, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] at hsum ⊢
    have hC : 0 ≤ 2 * Real.log 4 + 16 := by positivity
    have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hC hsqrt) (sub_nonneg.mpr hl)]
  H2 := by
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (PaperParams.eventually_l_ge 1)
    refine ⟨Real.log 4 + 4, T₀, ?_⟩
    intro T hT x hx hxupper
    have hl : 1 ≤ l T := hT₀ T hT
    have hsum := Cheb.sum_vonMangoldt_sq_le (x := x) (by linarith)
    simp only [zetaCoeffFamily_c, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] at hsum ⊢
    have hlog : Real.log x ≤ l T := by
      calc
        Real.log x ≤ Real.log (Real.exp (l T)) :=
          Real.log_le_log (by linarith) hxupper
        _ = l T := Real.log_exp _
    have hlog_sq : Real.log x ≤ l T ^ 2 := by nlinarith
    have hC : 0 ≤ Real.log 4 + 4 := by positivity
    have hx0 : 0 ≤ x := by linarith
    calc
      ∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, Λ N ^ 2 ≤
          (Real.log 4 + 4) * x * Real.log x := hsum
      _ ≤ (Real.log 4 + 4) * x * l T ^ 2 := by gcongr
  H3 := hH3
  D_cont := continuous_id
  D_nonneg := by
    intro s hs
    exact hs.1

/-- The uniform diagonal asymptotic follows from the pinned explicit
Chebyshev--Mertens estimate. -/
theorem zetaCoeffH3 : ZetaCoeffH3 := by
  intro ε hε
  obtain ⟨C, hC, hcheb⟩ := Cheb.sum_vonMangoldt_sq_div_eq
  let M : ℝ := max 1 (max (C / ε) (Real.log 2 ^ 2 / (2 * ε)))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (PaperParams.eventually_l_ge M)
  refine ⟨T₀, ?_⟩
  intro T hT y hy0 hyl
  have hlM : M ≤ l T := hT₀ T hT
  have hl1 : 1 ≤ l T := (le_max_left _ _).trans hlM
  have hl0 : 0 < l T := lt_of_lt_of_le zero_lt_one hl1
  have hmain : l T ^ 2 * ∫ s in (0 : ℝ)..(y / l T), zetaCoeffFamily.D s = y ^ 2 / 2 := by
    simp only [zetaCoeffFamily_D, integral_id]
    field_simp [hl0.ne']
    ring
  rw [hmain]
  have hsum :
      (∑ N ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
        ‖zetaCoeffFamily.c T N‖ ^ 2 / N) =
      ∑ N ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊, Λ N ^ 2 / N := by
    apply Finset.sum_congr rfl
    intro N _
    simp [zetaCoeffFamily, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [hsum]
  by_cases hy2 : Real.log 2 ≤ y
  · have hexp2 : (2 : ℝ) ≤ Real.exp y := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr hy2
    have hb := hcheb (Real.exp y) hexp2
    rw [Real.log_exp] at hb
    have hCl : C ≤ ε * l T := by
      have hCM : C / ε ≤ l T :=
        (le_max_left (C / ε) (Real.log 2 ^ 2 / (2 * ε))).trans
          ((le_max_right 1 _).trans hlM)
      rwa [div_le_iff₀' hε] at hCM
    have hCy : C * y ≤ ε * l T ^ 2 := by
      have hC0 : 0 ≤ C := hC.le
      have hε0 : 0 ≤ ε := hε.le
      calc
        C * y ≤ C * l T := mul_le_mul_of_nonneg_left hyl hC0
        _ ≤ (ε * l T) * l T := mul_le_mul_of_nonneg_right hCl hl0.le
        _ = ε * l T ^ 2 := by ring
    exact hb.trans hCy
  · have hylt2 : Real.exp y < 2 := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_lt_exp.mpr (lt_of_not_ge hy2)
    have hsum0 : (∑ N ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊, Λ N ^ 2 / N) = 0 := by
      apply Finset.sum_eq_zero
      intro N hN
      obtain ⟨hN0, hNfloor⟩ := Finset.mem_Ioc.mp hN
      have hNexp : (N : ℝ) ≤ Real.exp y :=
        (Nat.cast_le.mpr hNfloor).trans (Nat.floor_le (Real.exp_pos y).le)
      have hNlt : N < 2 := by exact_mod_cast hNexp.trans_lt hylt2
      have hN1 : N = 1 := by omega
      subst N
      simp [ArithmeticFunction.vonMangoldt_apply_one]
    rw [hsum0, zero_sub, abs_neg, abs_of_nonneg (by positivity : 0 ≤ y ^ 2 / 2)]
    have hylog : y ≤ Real.log 2 := (lt_of_not_ge hy2).le
    have hsmallM : Real.log 2 ^ 2 / (2 * ε) ≤ l T :=
      (le_max_right (C / ε) (Real.log 2 ^ 2 / (2 * ε))).trans
        ((le_max_right 1 _).trans hlM)
    have hsmall : Real.log 2 ^ 2 / 2 ≤ ε * l T := by
      have hm := mul_le_mul_of_nonneg_left hsmallM hε.le
      have heq : ε * (Real.log 2 ^ 2 / (2 * ε)) = Real.log 2 ^ 2 / 2 := by
        field_simp [hε.ne']
      rwa [heq] at hm
    have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hy2le : y ^ 2 / 2 ≤ Real.log 2 ^ 2 / 2 := by nlinarith
    have hεl : ε * l T ≤ ε * l T ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      nlinarith
    exact hy2le.trans (hsmall.trans hεl)

/-- The zeta coefficient family satisfies the complete generic hypothesis
package, unconditionally. -/
theorem zetaCoeffFamily_hyps : zetaCoeffFamily.Hyps :=
  zetaCoeffFamily_hyps_of_H3 zetaCoeffH3

lemma nucW_zetaCoeffFamily_eq_nuX (T X τ : ℝ) :
    nucW 1 X (zetaCoeffFamily.c T) τ = nuX X τ := by
  unfold zetaCoeffFamily
  simp only
  unfold nucW nuX
  rw [XiPrime.Pc_neg_vonMangoldt]
  ring

lemma GentryC_zetaCoeffFamily_eq_Gentry (P : Params) (T : ℝ) (k l : ℤ) :
    P.GentryC T (zetaCoeffFamily.c T) k l = P.Gentry T k l := by
  unfold Params.GentryC Params.GentryCW Params.Gentry
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [nucW_zetaCoeffFamily_eq_nuX]

/-- For `c_N=-Λ(N)`, the generic coefficient matrix is exactly the zeta
prime-side matrix. -/
theorem GpC_zetaCoeffFamily_eq_Gp (P : Params) (T : ℝ) :
    P.GpC T (zetaCoeffFamily.c T) = P.Gp T := by
  ext k l
  simp only [Params.GpC, Params.Gp]
  rw [GentryC_zetaCoeffFamily_eq_Gentry]

/-- The current-window zeta zero matrix and the fixed-coefficient matrix
agree eventually.  This uses the already-proved current-window admissibility
and the unconditional zeta explicit formula. -/
theorem eventually_Gz_eq_GpC_current {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    ∀ᶠ T in atTop,
      zetaZeroConfig.Gz (P.atV CurrentWindow.window T) T =
        (P.atV CurrentWindow.window T).GpC T (zetaCoeffFamily.c T) := by
  filter_upwards [Params.eventually_w8 hP] with T h8
  rw [GpC_zetaCoeffFamily_eq_Gp]
  exact GzGpV_of' hP CurrentWindow.window_even
    (fun T h8 => CurrentWindowAdmissibility.admWindow_current hP hcert h8)
    zetaZeroConfig paperInputs_zeta.EF h8

/-- Exact equality supplies the trace-transfer interface without `XiEF` or
re-expansion. -/
theorem current_zeta_traceTransfer {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    XiTraceTransfer zetaZeroConfig (P.atV CurrentWindow.window) zetaCoeffFamily := by
  have hEq := eventually_Gz_eq_GpC_current hP hcert
  constructor
  · intro δ hδ
    filter_upwards [hEq] with T hT
    rw [hT, sub_self, abs_zero]
    positivity
  · intro δ hδ
    filter_upwards [hEq] with T hT
    rw [hT]
    have hfr : 0 ≤ RHLinalg.frobSq
        ((P.atV CurrentWindow.window T).hat T
          ((P.atV CurrentWindow.window T).GpC T (zetaCoeffFamily.c T))) :=
      Assembly.frobSq_nonneg _
    have hN : 0 ≤ (zetaZeroConfig.N T (2 * T) : ℝ) := Nat.cast_nonneg _
    nlinarith

/-- Strongest unconditional transfer skeleton: once the generic prime-side
moments for `-Λ` are supplied, the actual zeta zero-side moments follow with
the same constant. -/
theorem current_zeta_gzMoments_of_coeffMoments {P : Params} {kappa : ℝ}
    (hP : P.Valid) (hcert : CurrentWindow.WindowCertificate)
    (hkappa : 0 ≤ kappa)
    (hM : CoeffMoments zetaZeroConfig (P.atV CurrentWindow.window)
      zetaCoeffFamily kappa) :
    GzMoments zetaZeroConfig (P.atV CurrentWindow.window) kappa :=
  gzMoments_of_transfer zetaZeroConfig _ zetaCoeffFamily hkappa hM
    (current_zeta_traceTransfer hP hcert)

/-- Positivity of the zeta current-window ratio constant at a fixed
`0 < λ ≤ 1`. -/
theorem current_cWin_id_pos {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    0 < cWin id P.lam CurrentWindow.window := by
  apply cWin_pos
  · have hm : 0 < CurrentWindow.windowMass CurrentWindow.window := by
      rw [← CurrentWindow.kernel_zero_eq_mass]
      exact CurrentWindow.kernel_zero_pos hcert
    exact ne_of_gt hm
  · exact CurrentWindowMoments.current_window_sq_integral_pos hcert
  · exact jWin_nonneg (fun x hx => hx.1)
      (CurrentWindow.window_nonneg_on_support hcert) hP.lam_pos.le
      hP.lam_le_one
  · exact hP.lam_pos

/-- The generic prime-side theorem, specialized natively to zeta.  After
the elementary coefficient bounds above, its only residual analytic premises
are the uniform diagonal asymptotic and the current-window autocorrelation
comparison. -/
theorem current_zeta_coeffMoments_of_H3_autocorr {P : Params}
    (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate)
    (hH3 : ZetaCoeffH3)
    (hg : ∀ᶠ T in atTop, ∀ y ∈ Icc (0 : ℝ) (P.L T),
      |AdmWindow.gv (P.phiV CurrentWindow.window T) y -
        P.L T * vConv CurrentWindow.window (y / P.L T)| ≤ 4 * P.w) :
    CoeffMoments zetaZeroConfig (P.atV CurrentWindow.window)
      zetaCoeffFamily (cWin id P.lam CurrentWindow.window)⁻¹ := by
  have hr₀ := CurrentWindowMoments.tendsto_cRatio_current_of_autocorr
    hP hcert continuousOn_id (fun x hx => hx.1) hg
  have hratio : Tendsto (fun T => ThmD.cRatio (P.lam1 T)
      (AdmWindow.av ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (AdmWindow.bv ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (JD id (AdmWindow.gv ((P.atV CurrentWindow.window T).phi T))
        (P.L T) (l T))) atTop
        (nhds (cWin id P.lam CurrentWindow.window)) := by
    convert hr₀ using 1
    funext T
    rw [Params.atV_phi_valid T hP CurrentWindow.window_even]
  exact current_coeffMoments hP hlam hcert
    (zetaCoeffFamily_hyps_of_H3 hH3) riemannVonMangoldt_zeta
    (current_cWin_id_pos hP hcert) hratio

/-- Zeta-native current-window zero-side moments.  In contrast to the former
`ξ'` specialization, this conclusion is about `zetaZeroConfig` and has the
linear density required by the paper's distance functional. -/
theorem current_zeta_gzMoments_of_H3_autocorr {P : Params}
    (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate)
    (hH3 : ZetaCoeffH3)
    (hg : ∀ᶠ T in atTop, ∀ y ∈ Icc (0 : ℝ) (P.L T),
      |AdmWindow.gv (P.phiV CurrentWindow.window T) y -
        P.L T * vConv CurrentWindow.window (y / P.L T)| ≤ 4 * P.w) :
    GzMoments zetaZeroConfig (P.atV CurrentWindow.window)
      (cWin id P.lam CurrentWindow.window)⁻¹ := by
  apply current_zeta_gzMoments_of_coeffMoments hP hcert
  · exact inv_nonneg.mpr (current_cWin_id_pos hP hcert).le
  · exact current_zeta_coeffMoments_of_H3_autocorr hP hlam hcert hH3 hg

/-- The sole current-window analytic estimate still needed by the zeta-native
moment route. -/
def CurrentAutocorr (P : Params) : Prop :=
  ∀ᶠ T in atTop, ∀ y ∈ Icc (0 : ℝ) (P.L T),
    |AdmWindow.gv (P.phiV CurrentWindow.window T) y -
      P.L T * vConv CurrentWindow.window (y / P.L T)| ≤ 4 * P.w

/-- With the coefficient asymptotic now proved, only `CurrentAutocorr`
remains before the zeta prime-side moments are unconditional. -/
theorem current_zeta_coeffMoments_of_autocorr {P : Params}
    (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate)
    (hg : CurrentAutocorr P) :
    CoeffMoments zetaZeroConfig (P.atV CurrentWindow.window)
      zetaCoeffFamily (cWin id P.lam CurrentWindow.window)⁻¹ :=
  current_zeta_coeffMoments_of_H3_autocorr hP hlam hcert zetaCoeffH3 hg

/-- Strongest zeta-native feasibility theorem: the actual zeta zero-side
moments follow from the single, explicitly named current-window
autocorrelation estimate. -/
theorem current_zeta_gzMoments_of_autocorr {P : Params}
    (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate)
    (hg : CurrentAutocorr P) :
    GzMoments zetaZeroConfig (P.atV CurrentWindow.window)
      (cWin id P.lam CurrentWindow.window)⁻¹ :=
  current_zeta_gzMoments_of_H3_autocorr hP hlam hcert zetaCoeffH3 hg

end Zeta23Ext.CurrentZetaNative
