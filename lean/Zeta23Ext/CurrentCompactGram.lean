/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentRetainedWithLoss
import Zeta23Ext.CurrentAnalyticInstantiation
import Zeta23Ext.CurrentWindowAdmissibility
import Zeta23Ext.CurrentWindowMoments
import Zeta23.PrimeSideA.EndsCore

/-!
# Exact compact-Gram reduction for the current window

This module removes the first algebraic layer from the remaining
compact-uniform Gram input.  For retained on-line zeros, an entry of the
normalized atom Gram matrix is exactly the finite Poisson kernel `Kfun`
divided by `a L^2`.  The upstream complement theorem then bounds its
difference from the infinite Poisson kernel by the two diagonal endpoint
tail masses `rho`.

Consequently, the analytic work still required for compact-uniform Gram
convergence is precisely:

* make those endpoint tail masses uniformly `o(a L^2)` on the retained
  interior; and
* identify the normalized infinite current-window kernel with
  `CurrentWindow.normalizedKernel` in the fixed scaled coordinate.

No asymptotic statement is assumed or proved in this file.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentCompactGram

open Zeta23
open Zeta23.PrimeSide
open Zeta23Ext.CurrentAnalyticInstantiation
open Zeta23Ext.CurrentRetainedWithLoss

variable {Z : ZeroConfig} {P : Params} {T : ℝ} {r : ℕ}

/-- The real ordinate attached to a retained on-line zero. -/
def ordinate (h : RetainedZeroData Z T r) (j : Fin r) : ℝ :=
  ((h.rho j : ZeroSide.ZI Z T) : ℂ).im

/-- Correctly scaled retained ordinate for an arbitrary parameter family. -/
def scaledY (h : RetainedZeroData Z T r) (P : Params) (j : Fin r) : ℝ :=
  scaledOrdinate P T (ordinate h j)

/-- The normalized infinite Poisson kernel at scaled separation `x`. -/
def normalizedInfiniteKernel (P : Params) (T x : ℝ) : ℝ :=
  P.PhiR T (2 * Real.pi * x / P.L T) / (P.a T * P.L T)

lemma gammaOf_retained (h : RetainedZeroData Z T r) (j : Fin r) :
    gammaOf ((h.rho j : ZeroSide.ZI Z T) : ℂ) = (ordinate h j : ℂ) :=
  ZeroSide.gammaOf_of_re_eq_half (h.onLine j)

lemma evalVec_retained_real (h : RetainedZeroData Z T r)
    (hreal : ZeroSide.PhiHatReal T P) (j : Fin r) (k : Fin (P.d T)) :
    ZeroSide.evalVec Z T P (h.rho j) k =
      (P.phiHatR T (ordinate h j - P.tau T (k : ℕ)) : ℂ) := by
  unfold ZeroSide.evalVec
  rw [gammaOf_retained h]
  norm_cast
  exact hreal _

lemma ordinate_sub_eq_scaledY_sub (h : RetainedZeroData Z T r)
    (hL : P.L T ≠ 0) (i j : Fin r) :
    ordinate h i - ordinate h j =
      -(2 * Real.pi * (scaledY h P j - scaledY h P i) / P.L T) := by
  unfold scaledY scaledOrdinate
  field_simp
  ring

/-- After scaling ordinates by the actual lattice length `P.L T`, the
normalized infinite Poisson kernel has an exact one-variable form. -/
theorem Kinf_div_eq_normalizedInfiniteKernel
    (h : RetainedZeroData Z T r)
    (hPhiEven : ∀ x : ℝ, P.PhiR T (-x) = P.PhiR T x)
    (hL : P.L T ≠ 0) (ha : P.a T ≠ 0) (i j : Fin r) :
    Kinf (P.toSetting T) (P.localFun T) (ordinate h i) (ordinate h j) /
        (P.a T * P.L T ^ 2) =
      normalizedInfiniteKernel P T (scaledY h P j - scaledY h P i) := by
  unfold Kinf normalizedInfiniteKernel
  simp only [Params.toSetting_L, Params.localFun_Phi]
  rw [ordinate_sub_eq_scaledY_sub h hL i j, hPhiEven]
  field_simp

/-- An exact entry of the normalized retained Gram matrix is the finite
Poisson kernel divided by `a L²`. -/
theorem gramEntry_eq_Kfun_div
    (h : RetainedZeroData Z T r)
    (hreal : ZeroSide.PhiHatReal T P)
    (hc : 0 < P.a T * P.L T ^ 2) (i j : Fin r) :
    ((h.V P)ᴴ * h.V P) i j =
      ((Kfun (P.toSetting T) (P.localFun T) (ordinate h i) (ordinate h j) /
        (P.a T * P.L T ^ 2) : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  unfold Kfun
  simp only [Params.toSetting_d, Params.localFun_phiHat, Params.toSetting_tau]
  rw [Finset.sum_div]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.conjTranspose_apply, RetainedZeroData.V]
  rw [evalVec_retained_real h hreal, evalVec_retained_real h hreal]
  change
    (starRingEnd ℂ)
        ((P.phiHatR T (ordinate h i - P.tau T (k : ℕ)) : ℂ) /
          (Real.sqrt (P.a T * P.L T ^ 2) : ℂ)) *
        ((P.phiHatR T (ordinate h j - P.tau T (k : ℕ)) : ℂ) /
          (Real.sqrt (P.a T * P.L T ^ 2) : ℂ)) = _
  rw [map_div₀, Complex.conj_ofReal]
  have hs : Real.sqrt (P.a T * P.L T ^ 2) ^ 2 = P.a T * P.L T ^ 2 :=
    Real.sq_sqrt hc.le
  have hsC :
      (Real.sqrt (P.a T * P.L T ^ 2) : ℂ) ^ 2 =
        (P.a T * P.L T ^ 2 : ℝ) := by exact_mod_cast hs
  have hs0 : (Real.sqrt (P.a T * P.L T ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 hc
  have ha0 : (P.a T : ℂ) ≠ 0 := by
    have : P.a T ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hc
      linarith
    exact_mod_cast this
  have hL0 : (P.L T : ℂ) ≠ 0 := by
    have : P.L T ≠ 0 := by
      intro hL
      rw [hL, zero_pow (by norm_num), mul_zero] at hc
      linarith
    exact_mod_cast this
  have hsconj :
      (starRingEnd ℂ) (Real.sqrt (P.a T * P.L T ^ 2) : ℂ) =
        (Real.sqrt (P.a T * P.L T ^ 2) : ℂ) := Complex.conj_ofReal _
  rw [hsconj]
  field_simp [hs0, ha0, hL0]
  rw [hsC]
  push_cast
  ring

/-- The exact finite-to-infinite kernel error, normalized in the atom units,
is bounded by the two diagonal omitted-tail masses. -/
theorem norm_gramEntry_sub_Kinf_le
    (h : RetainedZeroData Z T r)
    (hreal : ZeroSide.PhiHatReal T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    {c : ℝ}
    (hlocal : LocalHypsCoreW c (P.toSetting T) (P.localFun T))
    (i j : Fin r) :
    ‖((h.V P)ᴴ * h.V P) i j -
        ((Kinf (P.toSetting T) (P.localFun T) (ordinate h i) (ordinate h j) /
          (P.a T * P.L T ^ 2) : ℝ) : ℂ)‖ ≤
      (rho (P.toSetting T) (P.localFun T) (ordinate h i) +
        rho (P.toSetting T) (P.localFun T) (ordinate h j)) /
        (2 * (P.a T * P.L T ^ 2)) := by
  rw [gramEntry_eq_Kfun_div h hreal hc]
  have htail := abs_Kinf_sub_Kfun_le hlocal (ordinate h i) (ordinate h j)
    (s := 1) zero_lt_one
  simp only [one_mul, div_one] at htail
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hc0 : 0 < (P.a T * P.L T ^ 2) := hc
  rw [← sub_div]
  rw [abs_div, abs_of_pos hc0]
  have hsymm :
      |Kfun (P.toSetting T) (P.localFun T) (ordinate h i) (ordinate h j) -
          Kinf (P.toSetting T) (P.localFun T) (ordinate h i) (ordinate h j)| =
        |Kinf (P.toSetting T) (P.localFun T) (ordinate h i) (ordinate h j) -
          Kfun (P.toSetting T) (P.localFun T) (ordinate h i) (ordinate h j)| := by
    rw [abs_sub_comm]
  rw [hsymm]
  calc
    |Kinf (P.toSetting T) (P.localFun T) (ordinate h i) (ordinate h j) -
        Kfun (P.toSetting T) (P.localFun T) (ordinate h i) (ordinate h j)| /
          (P.a T * P.L T ^ 2)
        ≤ ((rho (P.toSetting T) (P.localFun T) (ordinate h i) +
              rho (P.toSetting T) (P.localFun T) (ordinate h j)) / 2) /
            (P.a T * P.L T ^ 2) := div_le_div_of_nonneg_right htail hc0.le
    _ = (rho (P.toSetting T) (P.localFun T) (ordinate h i) +
          rho (P.toSetting T) (P.localFun T) (ordinate h j)) /
        (2 * (P.a T * P.L T ^ 2)) := by ring

/-- Scaled-coordinate version of `norm_gramEntry_sub_Kinf_le`.  This is the
direct finite-height input for a later uniform tail estimate. -/
theorem norm_gramEntry_sub_normalizedInfiniteKernel_le
    (h : RetainedZeroData Z T r)
    (hreal : ZeroSide.PhiHatReal T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (hPhiEven : ∀ x : ℝ, P.PhiR T (-x) = P.PhiR T x)
    {c : ℝ}
    (hlocal : LocalHypsCoreW c (P.toSetting T) (P.localFun T))
    (i j : Fin r) :
    ‖((h.V P)ᴴ * h.V P) i j -
        (normalizedInfiniteKernel P T (scaledY h P j - scaledY h P i) : ℂ)‖ ≤
      (rho (P.toSetting T) (P.localFun T) (ordinate h i) +
        rho (P.toSetting T) (P.localFun T) (ordinate h j)) /
        (2 * (P.a T * P.L T ^ 2)) := by
  have hL : P.L T ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num), mul_zero] at hc
    linarith
  have ha : P.a T ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hc
    linarith
  rw [← Kinf_div_eq_normalizedInfiniteKernel h hPhiEven hL ha i j]
  exact norm_gramEntry_sub_Kinf_le h hreal hc hlocal i j

/-! ## Current-window specialization -/

/-- At every sufficiently large height, all abstract local hypotheses needed
by the exact truncation theorem are supplied by the proved current-window
admissibility and the certified lower mass bound. -/
theorem eventually_currentLocalHypsCore
    {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    ∀ᶠ T in Filter.atTop,
      LocalHypsCoreW
        (XiPrime.cMod P.ϱ
          CurrentWindowAdmissibility.factorA
          CurrentWindowAdmissibility.factorB)
        ((P.atV CurrentWindow.window T).toSetting T)
        ((P.atV CurrentWindow.window T).localFun T) := by
  filter_upwards [Params.eventually_w8 hP,
    CurrentWindowMoments.tendsto_bV_current hP hcert |>.eventually
      (Ioi_mem_nhds (by
        have hs := CurrentWindowMoments.current_window_sq_integral_pos hcert
        have hlower : (9 : ℝ) / 16 ≤
            CurrentWindow.windowSquareMass CurrentWindow.window := by
          unfold CurrentWindow.windowSquareMass
          have hint : IntervalIntegrable
              (fun s => CurrentWindow.window s ^ 2) MeasureTheory.volume
              (-(1 : ℝ) / 2) ((1 : ℝ) / 2) :=
            (CurrentWindow.continuous_window.pow 2).intervalIntegrable _ _
          have hm := intervalIntegral.integral_mono_on
            (a := -(1 : ℝ) / 2) (b := (1 : ℝ) / 2)
            (f := fun _ => (9 : ℝ) / 16)
            (g := fun s => CurrentWindow.window s ^ 2) (by norm_num)
            intervalIntegrable_const hint
            (fun s hs => by nlinarith [hcert.lower s hs])
          convert hm using 1 <;> norm_num
        linarith : (1 : ℝ) / 2 <
          CurrentWindow.windowSquareMass CurrentWindow.window))] with T h8 hb
  have hW := CurrentWindowAdmissibility.admWindow_current hP hcert h8
  have hl : 1 ≤ (P.toSetting T).l := by
    simpa only [Params.toSetting_l] using
      (show 1 ≤ Zeta23.l T from by
        have := h8
        have hw := hP.one_le_w
        simp only [Params.L] at h8
        nlinarith [hP.lam_le_one, hP.lam_pos])
  have hX : 1 ≤ (P.toSetting T).X := by
    simp only [Params.toSetting_X, Params.X]
    exact Real.one_le_exp (by
      have hL : 0 ≤ P.L T := by linarith [h8, hP.one_le_w]
      exact hL)
  rw [Params.atV_toSetting, Params.atV_localFun T hP CurrentWindow.window_even]
  exact (AdmWindow.localHypsCore (P.toSetting T) hW hP.lam_pos
    hP.lam_le_one hl hX hb.le).toCoreW

end Zeta23Ext.CurrentCompactGram
