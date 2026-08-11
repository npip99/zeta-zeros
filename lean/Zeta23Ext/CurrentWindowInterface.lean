/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindow
import Zeta23Ext.CurrentConstants

/-!
# Analytic interface for the current cosine window

This file gives the exact definitions of the one- and two-dimensional
functionals used by the paper and isolates the two finite inputs needed by the
current-window argument.  In particular, a value of `WindowCertificate` is an
input: this module does not claim to replay the external Arb computation.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Zeta23Ext.CurrentWindow

/-- The integral of a window over its full support interval. -/
def windowMass (v : ℝ → ℝ) : ℝ :=
  ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), v s

/-- The one-dimensional quadratic term in the denominator of `c1`. -/
def windowSquareMass (v : ℝ → ℝ) : ℝ :=
  ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), (v s) ^ 2

/-- The two-dimensional distance term in the denominator of `c1`. -/
def windowDistanceMass (v : ℝ → ℝ) : ℝ :=
  ∫ s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2),
    ∫ t in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), |s - t| * v s * v t

/-- The paper's exact endpoint functional
`c₁(v) = (∫v)² / (∫v² + ∫∫|s-t|v(s)v(t))`. -/
def c1 (v : ℝ → ℝ) : ℝ :=
  windowMass v ^ 2 / (windowSquareMass v + windowDistanceMass v)

/-- The paper's exact simple-zero baseline `H(v) = 2 - 1/c₁(v)`. -/
def H (v : ℝ → ℝ) : ℝ := 2 - 1 / c1 v

/-- The rational lower endpoint recorded by the current window certificate. -/
def Hcert : ℝ := 672457 / 1000000

lemma Hcert_eq_current : Hcert = Current.Hcert := rfl

/-- Exact proposition certified externally for the current cosine window.

The regularity and taper/ramp hypotheses used later in the analytic passage
are intentionally not hidden here.  This structure records only the finite
window facts proved by the Arb computation.
-/
structure WindowCertificate : Prop where
  lower : ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2), 3 / 4 ≤ window s
  upper : ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2), window s ≤ 1
  even : ∀ s : ℝ, window (-s) = window s
  nonincreasing :
    ∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      s ≤ t → window t ≤ window s
  H_lower : Hcert ≤ H window

/-- The cosine-polynomial window is continuous. -/
lemma continuous_window : Continuous window := by
  unfold window
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))

lemma intervalIntegrable_window :
    IntervalIntegrable window volume (-(1 : ℝ) / 2) ((1 : ℝ) / 2) :=
  continuous_window.intervalIntegrable _ _

/-- At zero, the cosine kernel is exactly the mass of the window. -/
lemma kernel_zero_eq_mass : kernel 0 = windowMass window := by
  unfold kernel windowMass
  simp

/-- The certified pointwise lower bound makes the kernel denominator positive. -/
lemma kernel_zero_pos (hcert : WindowCertificate) : 0 < kernel 0 := by
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (a := -(1 : ℝ) / 2) (b := (1 : ℝ) / 2)
    (f := fun _ => (3 : ℝ) / 4) (g := window) (by norm_num)
    intervalIntegrable_const intervalIntegrable_window hcert.lower
  rw [kernel_zero_eq_mass]
  refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) ?_
  calc
    (3 : ℝ) / 4 = ∫ _s in (-(1 : ℝ) / 2)..((1 : ℝ) / 2), (3 : ℝ) / 4 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      norm_num
    _ ≤ windowMass window := hmono

/-- Normalization is legitimate once the finite window certificate is supplied. -/
lemma normalizedKernel_zero (hcert : WindowCertificate) : normalizedKernel 0 = 1 := by
  unfold normalizedKernel
  exact div_self (ne_of_gt (kernel_zero_pos hcert))

/-- The certified lower bound implies nonnegativity on the support interval. -/
lemma window_nonneg_on_support (hcert : WindowCertificate) :
    ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2), 0 ≤ window s := by
  intro s hs
  exact le_trans (by norm_num) (hcert.lower s hs)

/-- The numerator of the normalized cosine kernel is bounded by its positive
zero-frequency denominator. -/
lemma abs_kernel_le_kernel_zero (hcert : WindowCertificate) (x : ℝ) :
    |kernel x| ≤ kernel 0 := by
  have hint : IntervalIntegrable
      (fun s => window s * Real.cos (2 * Real.pi * x * s)) volume
      (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
    exact (continuous_window.mul
      (Real.continuous_cos.comp
        (((continuous_const.mul continuous_const).mul continuous_const).mul continuous_id)))
      |>.intervalIntegrable _ _
  have habs := intervalIntegral.abs_integral_le_integral_abs
    (f := fun s => window s * Real.cos (2 * Real.pi * x * s))
    (μ := volume) (a := -(1 : ℝ) / 2) (b := (1 : ℝ) / 2) (by norm_num)
  have hpoint : ∀ s ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2),
      |window s * Real.cos (2 * Real.pi * x * s)| ≤ window s := by
    intro s hs
    rw [abs_mul, abs_of_nonneg (window_nonneg_on_support hcert s hs)]
    exact mul_le_of_le_one_right (window_nonneg_on_support hcert s hs)
      (Real.abs_cos_le_one _)
  have hmono := intervalIntegral.integral_mono_on (a := -(1 : ℝ) / 2)
    (b := (1 : ℝ) / 2) (by norm_num)
    (hint.abs) intervalIntegrable_window hpoint
  rw [kernel_zero_eq_mass]
  exact habs.trans hmono

/-- Every normalized cosine-kernel value lies in the unit interval in absolute
value. -/
lemma abs_normalizedKernel_le_one (hcert : WindowCertificate) (x : ℝ) :
    |normalizedKernel x| ≤ 1 := by
  rw [normalizedKernel, abs_div, abs_of_pos (kernel_zero_pos hcert)]
  exact (div_le_one (kernel_zero_pos hcert)).2 (abs_kernel_le_kernel_zero hcert x)

/-- The complete pair of finite, current-window inputs.  Supplying this value
does not supply any of the separate asymptotic, Gram-limit, or taper/ramp
hypotheses used by the analytic argument. -/
structure FiniteWindowInputs : Prop where
  localCertificate : LocalCertificate
  windowFacts : WindowCertificate

end Zeta23Ext.CurrentWindow
