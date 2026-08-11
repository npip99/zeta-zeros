/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentConstants
import Zeta23Ext.SqrtProfile
import Zeta23Ext.WeightedAggregation

/-!
# The current paper's single-block deduction

This module is the scalar seam between the exact weighted-window aggregation
and the sharp square-root defect profile.  The matrix input is deliberately
represented by the hypothesis

`sqrtProfile E ≤ traceDefect`.

Thus the theorem does not conceal either the analytic Gram-entry
approximation or the spectral profile bound.  In particular, the
approximation is required only in the small-span branch `span < D`; the
large-span branch is paid for entirely by pressure.
-/

noncomputable section
set_option maxHeartbeats 1000000

namespace Zeta23Ext.CurrentBlock

open Zeta23Ext.Current
open Zeta23Ext.SqrtProfile

/-- The exact span threshold `D = A / pressureCap`. -/
def D : ℝ := A / pressureCap

lemma D_eq : D = 714127 / 1500 := by
  unfold D A pressureCap
  norm_num

lemma D_pos : 0 < D := div_pos A_pos pressureCap_pos

lemma pressureCap_mul_D : pressureCap * D = A := by
  unfold D
  field_simp [pressureCap_pos.ne']

/-- At the current value `A > 1`, the sharp profile equals `R`. -/
lemma sqrtProfile_A : sqrtProfile A = R := by
  rw [sqrtProfile_of_one_le one_lt_A.le]
  rfl

lemma R_le_A : R ≤ A := by
  have hs := sqrtA_sq
  have hs0 := Real.sqrt_nonneg A
  unfold R
  nlinarith [sq_nonneg (Real.sqrt A - 1)]

lemma eta_le_one : eta ≤ 1 := by
  rw [eta, div_le_one A_pos]
  exact R_le_A

/-! ## The exact chord bound on `[0,A]` -/

/-- The line through `(0,0)` and `(A,h(A))` lies below the sharp profile on
`[0,A]`.  This is the exact inequality used in the small-energy branch. -/
lemma eta_mul_le_sqrtProfile {E : ℝ} (hE0 : 0 ≤ E) (hEA : E ≤ A) :
    eta * E ≤ sqrtProfile E := by
  rcases le_total E 1 with hE1 | h1E
  · rw [sqrtProfile_of_le_one hE1]
    exact mul_le_of_le_one_left hE0 eta_le_one
  · rw [sqrtProfile_of_one_le h1E]
    have hs0 : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
    have hsA0 : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
    have hs1 : 1 ≤ Real.sqrt E := Real.one_le_sqrt.mpr h1E
    have hsA1 : 1 ≤ Real.sqrt A := Real.one_le_sqrt.mpr one_lt_A.le
    have hsle : Real.sqrt E ≤ Real.sqrt A := Real.sqrt_le_sqrt hEA
    have hEsq : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE0
    have hAsq : Real.sqrt A ^ 2 = A := sqrtA_sq
    have hfactor1 : 0 ≤ Real.sqrt A - Real.sqrt E := sub_nonneg.mpr hsle
    have hfactor2 : 0 ≤ (2 * Real.sqrt A - 1) * Real.sqrt E - Real.sqrt A := by
      have hleft : 0 ≤ (Real.sqrt A - 1) * Real.sqrt E :=
        mul_nonneg (by linarith) hs0
      have hright : 0 ≤ Real.sqrt A * (Real.sqrt E - 1) :=
        mul_nonneg hsA0 (by linarith)
      nlinarith
    have hprod : 0 ≤ (Real.sqrt A - Real.sqrt E) *
        ((2 * Real.sqrt A - 1) * Real.sqrt E - Real.sqrt A) :=
      mul_nonneg hfactor1 hfactor2
    have hA0ne : A ≠ 0 := A_pos.ne'
    rw [eta]
    rw [div_mul_eq_mul_div, div_le_iff₀ A_pos]
    unfold R
    nlinarith

/-! ## Large-span and small-span branches -/

/-- At or beyond the exact threshold `D`, pressure alone pays the full
reward.  Equality `span = D` is deliberately included in this branch. -/
lemma large_span_pressure {span : ℝ} (hspan : D ≤ span) :
    R ≤ eta * pressureCap * span := by
  have hcoeff : 0 ≤ eta * pressureCap :=
    mul_nonneg eta_pos.le pressureCap_pos.le
  have hmul := mul_le_mul_of_nonneg_left hspan hcoeff
  rw [mul_assoc, pressureCap_mul_D] at hmul
  have hetaA : eta * A = R := by
    unfold eta
    field_simp [A_pos.ne']
  rwa [hetaA] at hmul

/-- **Single-block deduction, with the paper's exact case split.**

Inputs:

* `A ≤ kernelEnergy + pressureCap * span`, from weighted-window summation;
* in the small-span branch only, `kernelEnergy ≤ E + delta`, from uniform
  Gram-entry approximation on `[0,D]`;
* `sqrtProfile E ≤ traceDefect`, from the sharp spectral profile;
* nonnegativity of energy, span, and approximation error.

Conclusion:

`traceDefect + eta * pressureCap * span ≥ R - eta * delta`.
-/
theorem block_deduction
    {kernelEnergy E span delta traceDefect : ℝ}
    (hE0 : 0 ≤ E) (hspan0 : 0 ≤ span) (hdelta0 : 0 ≤ delta)
    (hkernel : A ≤ kernelEnergy + pressureCap * span)
    (happrox : span < D → kernelEnergy ≤ E + delta)
    (htrace : sqrtProfile E ≤ traceDefect) :
    R - eta * delta ≤ traceDefect + eta * pressureCap * span := by
  by_cases hlarge : D ≤ span
  · have hpressure := large_span_pressure hlarge
    have htrace0 : 0 ≤ traceDefect :=
      le_trans (sqrtProfile_nonneg hE0) htrace
    have herr0 : 0 ≤ eta * delta := mul_nonneg eta_pos.le hdelta0
    linarith
  · have hsmall : span < D := lt_of_not_ge hlarge
    have henergy : A ≤ E + delta + pressureCap * span := by
      linarith [hkernel, happrox hsmall]
    by_cases hAE : A ≤ E
    · have hprofile : R ≤ sqrtProfile E := by
        rw [← sqrtProfile_A]
        exact sqrtProfile_monoOn A_pos.le hE0 hAE
      have htraceR : R ≤ traceDefect := le_trans hprofile htrace
      have hpress0 : 0 ≤ eta * pressureCap * span :=
        mul_nonneg (mul_nonneg eta_pos.le pressureCap_pos.le) hspan0
      have herr0 : 0 ≤ eta * delta := mul_nonneg eta_pos.le hdelta0
      linarith
    · have hEA : E ≤ A := (lt_of_not_ge hAE).le
      have hchord : eta * E ≤ traceDefect :=
        le_trans (eta_mul_le_sqrtProfile hE0 hEA) htrace
      have hscaled : eta * A ≤ eta * (E + delta + pressureCap * span) :=
        mul_le_mul_of_nonneg_left henergy eta_pos.le
      have hetaA : eta * A = R := by
        unfold eta
        field_simp [A_pos.ne']
      rw [hetaA] at hscaled
      nlinarith

/-- Convenience form when the approximation has already been established
without exposing its small-span guard. -/
theorem block_deduction_of_approx
    {kernelEnergy E span delta traceDefect : ℝ}
    (hE0 : 0 ≤ E) (hspan0 : 0 ≤ span) (hdelta0 : 0 ≤ delta)
    (hkernel : A ≤ kernelEnergy + pressureCap * span)
    (happrox : kernelEnergy ≤ E + delta)
    (htrace : sqrtProfile E ≤ traceDefect) :
    R - eta * delta ≤ traceDefect + eta * pressureCap * span :=
  block_deduction hE0 hspan0 hdelta0 hkernel (fun _ => happrox) htrace

end Zeta23Ext.CurrentBlock
