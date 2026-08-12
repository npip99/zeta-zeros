/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindow
import Zeta23Ext.VerifiedCertificate
import Zeta23Ext.CurrentWindowInterface
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Closed sinc formula for the current kernel

This module connects the interval-integral definition used by the Lean proof
to the entire sinc expression evaluated by the numeric certificate.  The
removable zero-frequency case is proved rather than delegated to floating
point special handling.
-/

noncomputable section

open MeasureTheory

namespace Zeta23Ext.CurrentKernelFormula

/-- Fourier transform of the unit interval, including the removable case
`a = 0`. -/
theorem integral_cos_linear (a : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (a * s)) =
      Real.sinc (a / 2) := by
  by_cases ha : a = 0
  · subst a
    norm_num [Real.sinc_zero]
  · rw [Real.sinc_of_ne_zero (div_ne_zero ha (by norm_num))]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => Real.sin (a * s) / a)]
    · rw [show a * (-(1 : ℝ) / 2) = -(a / 2) by ring,
        show a * ((1 : ℝ) / 2) = a / 2 by ring, Real.sin_neg]
      field_simp [ha]
      ring
    · intro x _
      have hcomp := (Real.hasDerivAt_sin (a * x)).comp x
        (hasDerivAt_const_mul (x := x) a)
      simpa [ha] using hcomp.div_const a
    · exact (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- Integral of two cosine waves as the average of two entire sinc terms. -/
theorem integral_cos_mul_cos (a b : ℝ) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
      Real.cos (a * s) * Real.cos (b * s)) =
        (Real.sinc ((a - b) / 2) + Real.sinc ((a + b) / 2)) / 2 := by
  have hpoint : ∀ s : ℝ,
      Real.cos (a * s) * Real.cos (b * s) =
        (Real.cos ((a - b) * s) + Real.cos ((a + b) * s)) / 2 := by
    intro s
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    convert Real.two_mul_cos_mul_cos (a * s) (b * s) using 1 <;> ring_nf
  simp_rw [hpoint]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add,
    integral_cos_linear, integral_cos_linear]
  · exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  · exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- Entire closed form used by the interval verifier. -/
def closedKernel (x : ℝ) : ℝ :=
  ∑ j : Fin 7, CurrentWindow.coefficient j *
    (Real.sinc ((CurrentWindow.frequency j - 2 * Real.pi * x) / 2) +
      Real.sinc ((CurrentWindow.frequency j + 2 * Real.pi * x) / 2)) / 2

/-- The interval-integral kernel in the proof is exactly the verifier's
seven-term entire sinc sum, including every coincident-frequency case. -/
theorem kernel_eq_closedKernel (x : ℝ) :
    CurrentWindow.kernel x = closedKernel x := by
  unfold CurrentWindow.kernel CurrentWindow.window closedKernel
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    calc
      (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
          CurrentWindow.coefficient j * Real.cos (CurrentWindow.frequency j * s) *
            Real.cos (2 * Real.pi * x * s)) =
          CurrentWindow.coefficient j *
            (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
              Real.cos (CurrentWindow.frequency j * s) *
                Real.cos ((2 * Real.pi * x) * s)) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro s _
            ring
      _ = CurrentWindow.coefficient j *
          (Real.sinc ((CurrentWindow.frequency j - 2 * Real.pi * x) / 2) +
            Real.sinc ((CurrentWindow.frequency j + 2 * Real.pi * x) / 2)) / 2 := by
            rw [integral_cos_mul_cos]
            ring
  · intro j _
    exact (((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).const_mul _).mul
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).intervalIntegrable _ _

/-- The sinc-sum normalization denominator is strictly positive once the
finite pointwise window certificate is supplied. -/
theorem closedKernel_zero_pos (hcert : CurrentWindow.WindowCertificate) :
    0 < closedKernel 0 := by
  rw [← kernel_eq_closedKernel]
  exact CurrentWindow.kernel_zero_pos hcert

/-- Closed form for the exact normalized kernel consumed by the local
certificate. -/
theorem normalizedKernel_eq_closedKernel (x : ℝ) :
    CurrentWindow.normalizedKernel x = closedKernel x / closedKernel 0 := by
  rw [CurrentWindow.normalizedKernel, kernel_eq_closedKernel,
    kernel_eq_closedKernel]

/-- Closed form for the nonnegative pair potential. -/
theorem weight_eq_closedKernel (x : ℝ) :
    CurrentWindow.weight x = (closedKernel x / closedKernel 0) ^ 2 := by
  rw [CurrentWindow.weight, normalizedKernel_eq_closedKernel]

/-- A table proof may target the explicit sinc expression; this theorem
transfers it without leaving any integral/formula identification as an
external verifier assumption. -/
theorem dyadicTableSound_weight_iff
    (table : VerifiedCertificate.DyadicKernelTable) :
    table.Sound CurrentWindow.weight ↔
      table.Sound (fun x => (closedKernel x / closedKernel 0) ^ 2) := by
  unfold VerifiedCertificate.DyadicKernelTable.Sound
  simp_rw [weight_eq_closedKernel]

end Zeta23Ext.CurrentKernelFormula
