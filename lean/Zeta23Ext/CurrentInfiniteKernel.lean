/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentCompactGram
import Zeta23Ext.CurrentZetaAutocorr

/-!
# Infinite current-window kernel convergence

This module treats only the infinite Poisson kernel, in the lattice coordinate
set by the actual parameter length `P.L`.  Finite-lattice endpoint tails are a
separate issue.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Real Set MeasureTheory Filter Topology Matrix
open scoped ComplexOrder

namespace Zeta23Ext.CurrentInfiniteKernel

open Zeta23
open Zeta23Ext.CurrentCompactGram
open Zeta23Ext.CurrentZetaAutocorr
open Zeta23Ext.CurrentAnalyticInstantiation

/-- Exact normalization diagnostic: the actual atom coordinate is `lam`
times the paper ordinate currently stored in `RetainedZeroData.y`. -/
lemma scaledY_atV_eq_lam_mul_y {Z : ZeroConfig} {P : Params} {T : ℝ}
    {r : ℕ} (h : RetainedZeroData Z T r) (j : Fin r) :
    scaledY h (P.atV CurrentWindow.window T) j = P.lam * h.y j := by
  unfold scaledY Zeta23Ext.CurrentRetainedWithLoss.scaledOrdinate ordinate
    RetainedZeroData.y CurrentSpan.normalizedOrdinate
  simp only [Params.L, Params.atV_lam]
  ring

lemma scaledY_gap_atV_eq_lam_mul_y_gap {Z : ZeroConfig} {P : Params} {T : ℝ}
    {r : ℕ} (h : RetainedZeroData Z T r) (i j : Fin r) :
    scaledY h (P.atV CurrentWindow.window T) j -
        scaledY h (P.atV CurrentWindow.window T) i =
      P.lam * (h.y j - h.y i) := by
  rw [scaledY_atV_eq_lam_mul_y, scaledY_atV_eq_lam_mul_y]
  ring

lemma real_paperFT_eq_integral_mul_cos {f : ℝ → ℝ}
    (hf : Integrable f) (r : ℝ) :
    (paperFT (fun u => (f u : ℂ)) r).re =
      ∫ u, f u * Real.cos (r * u) := by
  have he : Integrable
      (fun u : ℝ => (f u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
    have ht := hf.ofReal.bdd_mul (c := 1)
      (show AEStronglyMeasurable
        (fun u : ℝ => Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) volume by
          fun_prop)
      (ae_of_all _ fun u => by
        rw [show Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I by
          push_cast
          ring,
          Complex.norm_exp_ofReal_mul_I])
    convert ht using 1
    funext u
    exact mul_comm _ _
  rw [paperFT_def, ← integral_re_C he]
  apply integral_congr_ae
  exact ae_of_all _ fun u => by
    change ((f u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).re = _
    rw [show Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
      ]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re]

private lemma integrable_mul_cos {f : ℝ → ℝ}
    (hf : Integrable f) (r : ℝ) :
    Integrable (fun u => f u * Real.cos (r * u)) := by
  have ht := hf.bdd_mul (c := 1)
    (show AEStronglyMeasurable (fun u : ℝ => Real.cos (r * u)) volume by
      fun_prop)
    (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact abs_cos_le_one _)
  convert ht using 1
  funext u
  exact mul_comm _ _

lemma abs_real_paperFT_sub_le_integral_abs {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    |(paperFT (fun u => (f u : ℂ)) r).re -
        (paperFT (fun u => (g u : ℂ)) r).re| ≤
      ∫ u, |f u - g u| := by
  rw [real_paperFT_eq_integral_mul_cos hf,
    real_paperFT_eq_integral_mul_cos hg,
    ← integral_sub (integrable_mul_cos hf r) (integrable_mul_cos hg r)]
  have heq : ∀ u : ℝ,
      f u * Real.cos (r * u) - g u * Real.cos (r * u) =
        (f u - g u) * Real.cos (r * u) := by intro u; ring
  rw [integral_congr_ae (ae_of_all _ heq)]
  calc
    |∫ u, (f u - g u) * Real.cos (r * u)|
        ≤ ∫ u, |(f u - g u) * Real.cos (r * u)| :=
          abs_integral_le_integral_abs
    _ ≤ ∫ u, |f u - g u| := by
      apply integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _)
        (hf.sub hg).abs
      exact ae_of_all _ fun u => by
        change |(f u - g u) * Real.cos (r * u)| ≤ |f u - g u|
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

lemma sharpCurrent_integrable {L : ℝ} :
    Integrable (sharpCurrent L) := by
  unfold sharpCurrent
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (((CurrentWindow.continuous_window.comp
      (continuous_id.div_const L)).continuousOn).integrableOn_compact isCompact_Icc)

lemma sharpCurrent_cos_transform {L x : ℝ} (hL : 0 < L) :
    ∫ u, sharpCurrent L u * Real.cos (2 * Real.pi * x / L * u) =
      L * CurrentWindow.kernel x := by
  unfold sharpCurrent
  have hind : ∀ u : ℝ,
      (Icc (-(L / 2)) (L / 2)).indicator
          (fun u => CurrentWindow.window (u / L)) u *
          Real.cos (2 * Real.pi * x / L * u) =
        (Icc (-(L / 2)) (L / 2)).indicator
          (fun u => CurrentWindow.window (u / L) *
            Real.cos (2 * Real.pi * x / L * u)) u := by
    intro u
    by_cases hu : u ∈ Icc (-(L / 2)) (L / 2) <;> simp [hu]
  rw [integral_congr_ae (ae_of_all _ hind),
    integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
  have hs := intervalIntegral.integral_comp_div
    (a := -(L / 2)) (b := L / 2)
    (f := fun s => CurrentWindow.window s *
      Real.cos (2 * Real.pi * x * s)) hL.ne'
  have e1 : -(L / 2) / L = -(1 : ℝ) / 2 := by field_simp
  have e2 : (L / 2) / L = (1 : ℝ) / 2 := by field_simp
  rw [e1, e2, smul_eq_mul] at hs
  unfold CurrentWindow.kernel
  rw [← hs]
  apply intervalIntegral.integral_congr
  intro u _
  field_simp

/-- Quantitative convergence of the unnormalized infinite current-window
kernel.  The estimate is global in the scaled frequency `x`. -/
theorem abs_VPhiR_sub_L_kernel_le {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {T x : ℝ}
    (h8 : 8 * P.w ≤ P.L T) :
    |AdmWindow.VPhiR (P.phiV CurrentWindow.window T)
          (2 * Real.pi * x / P.L T) -
        P.L T * CurrentWindow.kernel x| ≤ 2 * P.w := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hW := CurrentWindowAdmissibility.admWindow_current hP hcert h8
  have hphi : Integrable
      (fun u => P.phiV CurrentWindow.window T u ^ 2) :=
    hW.integrable_pow (by norm_num)
  have hsharp : Integrable (sharpCurrent (P.L T)) := sharpCurrent_integrable
  have hbound := abs_real_paperFT_sub_le_integral_abs hphi hsharp
    (2 * Real.pi * x / P.L T)
  change |(paperFT (fun u =>
      ((P.phiV CurrentWindow.window T u ^ 2 : ℝ) : ℂ))
      ((2 * Real.pi * x / P.L T : ℝ) : ℂ)).re -
      P.L T * CurrentWindow.kernel x| ≤ 2 * P.w
  rw [← sharpCurrent_cos_transform hL,
    ← real_paperFT_eq_integral_mul_cos hsharp]
  exact hbound.trans (integral_abs_phiV_sq_sub_sharp hP hcert (by linarith))

lemma normalizedInfiniteKernel_atV_eq {P : Params} (hP : P.Valid)
    (T x : ℝ) :
    normalizedInfiniteKernel (P.atV CurrentWindow.window T) T x =
      AdmWindow.VPhiR (P.phiV CurrentWindow.window T)
          (2 * Real.pi * x / P.L T) /
        (AdmWindow.av (P.phiV CurrentWindow.window T) (P.L T) * P.L T) := by
  unfold normalizedInfiniteKernel
  change (((P.atV CurrentWindow.window T).localFun T).Phi
        (2 * Real.pi * x / (P.atV CurrentWindow.window T).L T)) /
      ((P.atV CurrentWindow.window T).a T *
        (P.atV CurrentWindow.window T).L T) = _
  rw [Params.atV_localFun T hP CurrentWindow.window_even,
    Params.atV_a T hP CurrentWindow.window_even,
    Params.atV_L]
  rfl

private lemma ratio_error_bound {A B k m e L : ℝ}
    (hm : 0 < m) (hL : 0 < L) (hB : 0 < B) (he : 0 ≤ e)
    (hA : |A - L * k| ≤ e) (hBclose : |B - L * m| ≤ e)
    (hk : |k| ≤ m) (hsmall : 2 * e ≤ L * m) :
    |A / B - k / m| ≤ 4 * e / (L * m) := by
  have hBm : 0 < B * m := mul_pos hB hm
  have hLm : 0 < L * m := mul_pos hL hm
  have hnum : |m * (A - L * k) - k * (B - L * m)| ≤ 2 * m * e := by
    calc
      |m * (A - L * k) - k * (B - L * m)|
          ≤ |m * (A - L * k)| + |k * (B - L * m)| := abs_sub _ _
      _ = m * |A - L * k| + |k| * |B - L * m| := by
        rw [abs_mul, abs_mul, abs_of_pos hm]
      _ ≤ m * e + m * e := by gcongr
      _ = 2 * m * e := by ring
  have hBlower : L * m / 2 ≤ B := by
    have hneg := neg_le_of_abs_le hBclose
    linarith
  have hid : A / B - k / m =
      (m * (A - L * k) - k * (B - L * m)) / (B * m) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hBm]
  rw [div_le_iff₀ hBm, div_mul_eq_mul_div]
  apply (le_div_iff₀ hLm).2
  have hm0 : 0 ≤ m := hm.le
  have he0 : 0 ≤ e := he
  nlinarith [mul_nonneg (sub_nonneg.mpr hBlower) (mul_nonneg hm0 he0),
    mul_nonneg (sub_nonneg.mpr hnum) hLm.le]

/-- A global-in-frequency error estimate for the normalized infinite kernel.
In particular, compactness of the frequency set is not needed at this layer. -/
theorem abs_normalizedInfiniteKernel_atV_sub_le {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {T x : ℝ}
    (h8 : 8 * P.w ≤ P.L T)
    (hsmall : 4 * P.w ≤
      P.L T * CurrentWindow.kernel 0) :
    |normalizedInfiniteKernel (P.atV CurrentWindow.window T) T x -
        CurrentWindow.normalizedKernel x| ≤
      8 * P.w / (P.L T * CurrentWindow.kernel 0) := by
  let A := AdmWindow.VPhiR (P.phiV CurrentWindow.window T)
    (2 * Real.pi * x / P.L T)
  let B := AdmWindow.av (P.phiV CurrentWindow.window T) (P.L T) * P.L T
  let k := CurrentWindow.kernel x
  let m := CurrentWindow.kernel 0
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hm : 0 < m := by exact CurrentWindow.kernel_zero_pos hcert
  have hA : |A - P.L T * k| ≤ 2 * P.w := by
    exact abs_VPhiR_sub_L_kernel_le hP hcert h8
  have hBexact : B = AdmWindow.VPhiR
      (P.phiV CurrentWindow.window T) 0 := by
    have hW := CurrentWindowAdmissibility.admWindow_current hP hcert h8
    symm
    exact hW.VPhiR_zero
  have hBclose : |B - P.L T * m| ≤ 2 * P.w := by
    rw [hBexact]
    simpa [m] using (abs_VPhiR_sub_L_kernel_le hP hcert h8 (x := 0))
  have hB : 0 < B := by
    have hneg := neg_le_of_abs_le hBclose
    have hw0 : 0 < P.w := by linarith [hP.one_le_w]
    linarith
  have hk : |k| ≤ m := CurrentWindow.abs_kernel_le_kernel_zero hcert x
  have hw0 : 0 ≤ 2 * P.w := by linarith [hP.one_le_w]
  rw [normalizedInfiniteKernel_atV_eq hP,
    CurrentWindow.normalizedKernel]
  change |A / B - k / m| ≤ _
  have hr := ratio_error_bound hm hL hB hw0
    hA hBclose hk (by linarith)
  convert hr using 1 <;> ring

/-- Explicit uniform error for the normalized infinite current kernel. -/
def infiniteKernelError (P : Params) (T : ℝ) : ℝ :=
  8 * P.w / (P.L T * CurrentWindow.kernel 0)

theorem tendsto_infiniteKernelError {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    Tendsto (infiniteKernelError P) atTop (nhds 0) := by
  have hm : 0 < CurrentWindow.kernel 0 := CurrentWindow.kernel_zero_pos hcert
  have hden : Tendsto (fun T => P.L T * CurrentWindow.kernel 0) atTop atTop := by
    have ht := (Params.tendsto_L_of_valid hP).const_mul_atTop hm
    exact ht.congr (fun T => by ring)
  change Tendsto
    (fun T => (8 * P.w) / (P.L T * CurrentWindow.kernel 0)) atTop (nhds 0)
  exact tendsto_const_nhds.div_atTop hden

/-- The infinite Poisson kernel converges uniformly on the whole real scaled
frequency axis to the current normalized kernel. -/
theorem uniformly_normalizedInfiniteKernel_current {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    Tendsto (infiniteKernelError P) atTop (nhds 0) ∧
      ∀ᶠ T in atTop, 0 ≤ infiniteKernelError P T ∧
        ∀ x : ℝ,
          |normalizedInfiniteKernel (P.atV CurrentWindow.window T) T x -
              CurrentWindow.normalizedKernel x| ≤ infiniteKernelError P T := by
  refine ⟨tendsto_infiniteKernelError hP hcert, ?_⟩
  have hm : 0 < CurrentWindow.kernel 0 := CurrentWindow.kernel_zero_pos hcert
  filter_upwards [
    (Params.tendsto_L_of_valid hP).eventually_ge_atTop (8 * P.w),
    (Params.tendsto_L_of_valid hP).eventually_ge_atTop
      (4 * P.w / CurrentWindow.kernel 0)] with T h8 hsmall
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  constructor
  · unfold infiniteKernelError
    exact div_nonneg (by linarith [hP.one_le_w]) (mul_nonneg hL.le hm.le)
  · intro x
    apply abs_normalizedInfiniteKernel_atV_sub_le hP hcert h8
    exact (div_le_iff₀ hm).mp hsmall

/-! ## Honest finite-to-infinite residual -/

/-- Uniform vanishing of the two lattice-complement tails, normalized in the
same units as the atom Gram matrix.  Dyadic membership alone does not provide
this: a separate scaled interior-margin construction is required. -/
def UniformNormalizedRhoTail {Z : ZeroConfig} (P : Params)
    {r : ℝ → ℕ} (ret : ∀ T, RetainedZeroData Z T (r T)) : Prop :=
  ∃ tail : ℝ → ℝ, Tendsto tail atTop (nhds 0) ∧
    ∀ᶠ T in atTop, 0 ≤ tail T ∧
      ∀ j : Fin (r T),
        PrimeSide.rho ((P.atV CurrentWindow.window T).toSetting T)
            ((P.atV CurrentWindow.window T).localFun T)
            (ordinate (ret T) j) /
          ((P.atV CurrentWindow.window T).a T *
            (P.atV CurrentWindow.window T).L T ^ 2) ≤ tail T

/-- The `2/|r|` branch of the generic Fourier majorant gives the scale-sharp
tail integral needed near a moving lattice endpoint. -/
theorem setIntegral_psiA_sq_Ioi_le_four_div
    {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) {Delta : ℝ} (hDelta : 0 < Delta) :
    ∫ r in Ioi Delta, PrimeSide.psiA c p r ^ 2 ≤ 4 / Delta := by
  have hmaj : IntegrableOn (fun r : ℝ => 4 * r ^ (-2 : ℝ)) (Ioi Delta) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hDelta).const_mul 4
  calc
    ∫ r in Ioi Delta, PrimeSide.psiA c p r ^ 2
        ≤ ∫ r in Ioi Delta, 4 * r ^ (-2 : ℝ) := by
      refine setIntegral_mono_on hF.psi_sq_integrable.integrableOn hmaj
        measurableSet_Ioi fun r hr => ?_
      have hr0 : 0 < r := hDelta.trans hr
      have hpsi := PrimeSide.psiA_le_div_abs (cϱ := c) (p := p) hr0.ne'
      rw [abs_of_pos hr0] at hpsi
      calc
        PrimeSide.psiA c p r ^ 2 ≤ (2 / r) ^ 2 :=
          pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF r) hpsi 2
        _ = 4 * r ^ (-2 : ℝ) := by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_neg hr0.le, Real.rpow_natCast]
          field_simp
          norm_num
    _ = 4 / Delta := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hDelta]
      norm_num
      rw [Real.rpow_neg_one, div_eq_mul_inv]

/-- Scale-sharp pointwise bound for the omitted-grid majorant. -/
theorem Wfun_le_four {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) {Delta : ℝ} (hDelta : 0 < Delta) :
    PrimeSide.Wfun c p Delta ≤
      (2 / Delta) ^ 2 + p.h⁻¹ * (4 / Delta) := by
  unfold PrimeSide.Wfun
  have hpsi := PrimeSide.psiA_le_div_abs (cϱ := c) (p := p) hDelta.ne'
  rw [abs_of_pos hDelta] at hpsi
  apply add_le_add
  · exact pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF Delta) hpsi 2
  · exact mul_le_mul_of_nonneg_left
      (setIntegral_psiA_sq_Ioi_le_four_div hF hDelta)
      (inv_nonneg.mpr (PrimeSide.Setting.h_pos hF.L_pos).le)

/-- Correctly scaled compact-Gram statement.  Its target coordinate is the
actual atom coordinate `scaledY`, not the unscaled paper ordinate `y`. -/
def CompactUniformScaledCurrentGram {Z : ZeroConfig} (P : Params)
    {r : ℝ → ℕ} (ret : ∀ T, RetainedZeroData Z T (r T)) : Prop :=
  ∀ D : ℝ, 0 < D → ∃ err : ℝ → ℝ,
    Tendsto err atTop (nhds 0) ∧
    ∀ᶠ T in atTop, 0 ≤ err T ∧
      ∀ i j : Fin (r T),
        |scaledY (ret T) (P.atV CurrentWindow.window T) j -
            scaledY (ret T) (P.atV CurrentWindow.window T) i| ≤ D →
        ‖(((ret T).V (P.atV CurrentWindow.window T))ᴴ *
              (ret T).V (P.atV CurrentWindow.window T)) i j -
            (CurrentWindow.normalizedKernel
              (scaledY (ret T) (P.atV CurrentWindow.window T) j -
                scaledY (ret T) (P.atV CurrentWindow.window T) i) : ℂ)‖ ≤ err T

/-- Once a genuine interior-tail estimate is supplied, the exact truncation
theorem and the proved global infinite-kernel limit give the correctly scaled
compact Gram theorem. -/
theorem compactUniformScaledCurrentGram_of_rhoTail
    {Z : ZeroConfig} {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate)
    {r : ℝ → ℕ} (ret : ∀ T, RetainedZeroData Z T (r T))
    (htail : UniformNormalizedRhoTail P ret) :
    CompactUniformScaledCurrentGram P ret := by
  obtain ⟨tail, htail0, htailE⟩ := htail
  intro D _hD
  refine ⟨fun T => tail T + infiniteKernelError P T,
    (by simpa using htail0.add (tendsto_infiniteKernelError hP hcert)), ?_⟩
  have hinf := (uniformly_normalizedInfiniteKernel_current hP hcert).2
  have hlocal := eventually_currentLocalHypsCore hP hcert
  filter_upwards [htailE, hinf, hlocal,
    (Params.tendsto_L_of_valid hP).eventually_ge_atTop (8 * P.w)] with
      T htailT hinfT hlocalT h8
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hW := CurrentWindowAdmissibility.admWindow_current hP hcert h8
  have haHalf := CurrentAnalyticBridge.current_a_half hP hcert h8 hW
  have ha : 0 < (P.atV CurrentWindow.window T).a T := by linarith
  have hc : 0 < (P.atV CurrentWindow.window T).a T *
      (P.atV CurrentWindow.window T).L T ^ 2 := by
    simp only [Params.atV_L]
    positivity
  have hPhiEven : ∀ x : ℝ,
      (P.atV CurrentWindow.window T).PhiR T (-x) =
        (P.atV CurrentWindow.window T).PhiR T x := by
    intro x
    change (((P.atV CurrentWindow.window T).localFun T).Phi (-x)) =
      (((P.atV CurrentWindow.window T).localFun T).Phi x)
    rw [Params.atV_localFun T hP CurrentWindow.window_even]
    exact hW.VPhiR_even x
  constructor
  · exact add_nonneg htailT.1 hinfT.1
  · intro i j _hij
    have hfinite := norm_gramEntry_sub_normalizedInfiniteKernel_le
      (ret T) ZeroSide.phiHatReal hc hPhiEven hlocalT i j
    have hinfinite := hinfT.2
      (scaledY (ret T) (P.atV CurrentWindow.window T) j -
        scaledY (ret T) (P.atV CurrentWindow.window T) i)
    have hden : 0 < (P.atV CurrentWindow.window T).a T *
        (P.atV CurrentWindow.window T).L T ^ 2 := hc
    have htailBound :
        (PrimeSide.rho ((P.atV CurrentWindow.window T).toSetting T)
              ((P.atV CurrentWindow.window T).localFun T) (ordinate (ret T) i) +
            PrimeSide.rho ((P.atV CurrentWindow.window T).toSetting T)
              ((P.atV CurrentWindow.window T).localFun T) (ordinate (ret T) j)) /
          (2 * ((P.atV CurrentWindow.window T).a T *
            (P.atV CurrentWindow.window T).L T ^ 2)) ≤ tail T := by
      have hi := htailT.2 i
      have hj := htailT.2 j
      rw [show
        (PrimeSide.rho ((P.atV CurrentWindow.window T).toSetting T)
              ((P.atV CurrentWindow.window T).localFun T) (ordinate (ret T) i) +
            PrimeSide.rho ((P.atV CurrentWindow.window T).toSetting T)
              ((P.atV CurrentWindow.window T).localFun T) (ordinate (ret T) j)) /
            (2 * ((P.atV CurrentWindow.window T).a T *
              (P.atV CurrentWindow.window T).L T ^ 2)) =
          ((PrimeSide.rho ((P.atV CurrentWindow.window T).toSetting T)
                ((P.atV CurrentWindow.window T).localFun T) (ordinate (ret T) i) /
              ((P.atV CurrentWindow.window T).a T *
                (P.atV CurrentWindow.window T).L T ^ 2)) +
            (PrimeSide.rho ((P.atV CurrentWindow.window T).toSetting T)
                ((P.atV CurrentWindow.window T).localFun T) (ordinate (ret T) j) /
              ((P.atV CurrentWindow.window T).a T *
                (P.atV CurrentWindow.window T).L T ^ 2))) / 2 by
          field_simp]
      linarith
    calc
      ‖(((ret T).V (P.atV CurrentWindow.window T))ᴴ *
              (ret T).V (P.atV CurrentWindow.window T)) i j -
            (CurrentWindow.normalizedKernel
              (scaledY (ret T) (P.atV CurrentWindow.window T) j -
                scaledY (ret T) (P.atV CurrentWindow.window T) i) : ℂ)‖
          ≤ ‖(((ret T).V (P.atV CurrentWindow.window T))ᴴ *
                  (ret T).V (P.atV CurrentWindow.window T)) i j -
                (normalizedInfiniteKernel (P.atV CurrentWindow.window T) T
                  (scaledY (ret T) (P.atV CurrentWindow.window T) j -
                    scaledY (ret T) (P.atV CurrentWindow.window T) i) : ℂ)‖ +
              ‖(normalizedInfiniteKernel (P.atV CurrentWindow.window T) T
                  (scaledY (ret T) (P.atV CurrentWindow.window T) j -
                    scaledY (ret T) (P.atV CurrentWindow.window T) i) : ℂ) -
                (CurrentWindow.normalizedKernel
                  (scaledY (ret T) (P.atV CurrentWindow.window T) j -
                    scaledY (ret T) (P.atV CurrentWindow.window T) i) : ℂ)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ tail T + infiniteKernelError P T := by
        gcongr
        · exact hfinite.trans htailBound
        · simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            using hinfinite

end Zeta23Ext.CurrentInfiniteKernel
