/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentKernelDerivatives
import Mathlib.Analysis.Calculus.LHopital

/-!
# Total derivatives for the current closed kernel

The quotient expressions in `SincDerivativeCertificate` intentionally only
describe derivatives away from the removable point.  Tangent ranges can cross
such a point, so this module supplies total first and second sinc derivatives
and connects the resulting current-window expression to genuine derivatives
at every real argument.
-/

noncomputable section

open Real Set Filter Topology
open scoped BigOperators

namespace Zeta23Ext.CurrentKernelTotalDerivatives

open CurrentWindow
open CurrentKernelFormula
open CurrentKernelDerivatives
open SincDerivativeCertificate

/-- The genuine first derivative of sinc, including its removable value. -/
def sincD1Total (x : ℝ) : ℝ := if x = 0 then 0 else sincD1 x

/-- The genuine second derivative of sinc, including its removable value. -/
def sincD2Total (x : ℝ) : ℝ := if x = 0 then -(1 / 3 : ℝ) else sincD2 x

@[simp] lemma sincD1Total_zero : sincD1Total 0 = 0 := by simp [sincD1Total]
@[simp] lemma sincD2Total_zero : sincD2Total 0 = -(1 / 3 : ℝ) := by simp [sincD2Total]

lemma sincD1Total_eq {x : ℝ} (hx : x ≠ 0) : sincD1Total x = sincD1 x := by
  simp [sincD1Total, hx]

lemma sincD2Total_eq {x : ℝ} (hx : x ≠ 0) : sincD2Total x = sincD2 x := by
  simp [sincD2Total, hx]

private lemma tendsto_cos_sub_one_div_two_mul :
    Tendsto (fun x : ℝ => (Real.cos x - 1) / (2 * x))
      (𝓝[≠] 0) (𝓝 0) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
      (f := fun x : ℝ => Real.cos x - 1) (f' := fun x => -Real.sin x)
      (g := fun x : ℝ => 2 * x) (g' := fun _ => (2 : ℝ))
  · exact Filter.Eventually.of_forall fun x => (Real.hasDerivAt_cos x).sub_const 1
  · exact Filter.Eventually.of_forall fun x => by
      have h := (hasDerivAt_id x).const_mul 2
      simpa only [id_eq] using h.congr_deriv (by norm_num)
  · exact Filter.Eventually.of_forall fun _ => by norm_num
  · exact tendsto_nhdsWithin_of_tendsto_nhds <| by
      have h := ((Real.hasDerivAt_cos 0).sub_const 1).continuousAt
      have ht : Tendsto (fun x : ℝ => Real.cos x - 1) (nhds 0)
          (nhds ((fun x : ℝ => Real.cos x - 1) 0)) := h
      simpa only [show (fun x : ℝ => Real.cos x - 1) 0 = 0 by norm_num] using ht
  · exact tendsto_nhdsWithin_of_tendsto_nhds <| by
      have h := (((hasDerivAt_id (0 : ℝ)).const_mul 2).continuousAt)
      have h' : ContinuousAt (fun x : ℝ => 2 * x) 0 := by simpa [id] using h
      have ht : Tendsto (fun x : ℝ => 2 * x) (nhds 0)
          (nhds ((fun x : ℝ => 2 * x) 0)) := h'
      simpa only [show (fun x : ℝ => 2 * x) 0 = 0 by norm_num] using ht
  · exact tendsto_nhdsWithin_of_tendsto_nhds <| by
      have h := (((Real.hasDerivAt_sin 0).neg.div_const 2).continuousAt)
      have h' : ContinuousAt (fun x : ℝ => -Real.sin x / 2) 0 := by
        simpa using h
      have ht : Tendsto (fun x : ℝ => -Real.sin x / 2) (nhds 0)
          (nhds ((fun x : ℝ => -Real.sin x / 2) 0)) := h'
      simpa only [show (fun x : ℝ => -Real.sin x / 2) 0 = 0 by norm_num] using ht

private lemma tendsto_sinc_slope_zero :
    Tendsto (slope Real.sinc 0) (𝓝[≠] 0) (𝓝 0) := by
  have hquot : Tendsto (fun x : ℝ => (Real.sin x - x) / x ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    apply HasDerivAt.lhopital_zero_nhdsNE
        (f := fun x : ℝ => Real.sin x - x) (f' := fun x => Real.cos x - 1)
        (g := fun x : ℝ => x ^ 2) (g' := fun x => 2 * x)
    · exact Filter.Eventually.of_forall fun x =>
        (Real.hasDerivAt_sin x).sub (hasDerivAt_id x)
    · exact Filter.Eventually.of_forall fun x => by
        simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hasDerivAt_pow 2 x
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero (by norm_num) hx
    · exact tendsto_nhdsWithin_of_tendsto_nhds <| by
        have h := ((Real.hasDerivAt_sin 0).sub (hasDerivAt_id 0)).continuousAt
        have h' : ContinuousAt (fun x : ℝ => Real.sin x - x) 0 := by
          apply h.congr_of_eventuallyEq
          exact Filter.Eventually.of_forall fun x => by simp [id]
        have ht : Tendsto (fun x : ℝ => Real.sin x - x) (nhds 0)
            (nhds ((fun x : ℝ => Real.sin x - x) 0)) := h'
        simpa only [show (fun x : ℝ => Real.sin x - x) 0 = 0 by norm_num] using ht
    · exact tendsto_nhdsWithin_of_tendsto_nhds <| by
        have h := (hasDerivAt_pow 2 (0 : ℝ)).continuousAt
        have ht : Tendsto (fun x : ℝ => x ^ 2) (nhds 0)
            (nhds ((fun x : ℝ => x ^ 2) 0)) := h
        simpa only [show (fun x : ℝ => x ^ 2) 0 = 0 by norm_num] using ht
    · exact tendsto_cos_sub_one_div_two_mul
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [slope_fun_def_field]
  simp only [Real.sinc_zero, sub_zero]
  rw [Real.sinc_of_ne_zero hx]
  have hx0 : x ≠ 0 := hx
  field_simp [hx0]

/-- Sinc has its correctly totalized first derivative at every real point. -/
theorem hasDerivAt_sinc_total (x : ℝ) :
    HasDerivAt Real.sinc (sincD1Total x) x := by
  by_cases hx : x = 0
  · subst x
    rw [hasDerivAt_iff_tendsto_slope, sincD1Total_zero]
    exact tendsto_sinc_slope_zero
  · simpa [sincD1Total, hx] using hasDerivAt_sinc hx

private lemma tendsto_sincD1_div_zero :
    Tendsto (fun x : ℝ => sincD1 x / x) (𝓝[≠] 0) (𝓝 (-(1 / 3 : ℝ))) := by
  have hquot : Tendsto
      (fun x : ℝ => (x * Real.cos x - Real.sin x) / x ^ 3)
      (𝓝[≠] 0) (𝓝 (-(1 / 3 : ℝ))) := by
    apply HasDerivAt.lhopital_zero_nhdsNE
        (f := fun x : ℝ => x * Real.cos x - Real.sin x)
        (f' := fun x => -(x * Real.sin x))
        (g := fun x : ℝ => x ^ 3) (g' := fun x => 3 * x ^ 2)
    · exact Filter.Eventually.of_forall fun x => by
        have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)).sub
          (Real.hasDerivAt_sin x)
        simp only [id_eq] at h
        exact h.congr_deriv (by ring)
    · exact Filter.Eventually.of_forall fun x => by
        simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_two] using hasDerivAt_pow 3 x
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)
    · exact tendsto_nhdsWithin_of_tendsto_nhds <| by
        have h := ((hasDerivAt_id 0).mul (Real.hasDerivAt_cos 0)).sub
          (Real.hasDerivAt_sin 0)
        have hc := h.continuousAt
        have hc' : ContinuousAt (fun x : ℝ =>
            x * Real.cos x - Real.sin x) 0 := by
          apply hc.congr_of_eventuallyEq
          exact Filter.Eventually.of_forall fun x => by simp [id]
        have ht : Tendsto (fun x : ℝ => x * Real.cos x - Real.sin x) (nhds 0)
            (nhds ((fun x : ℝ => x * Real.cos x - Real.sin x) 0)) := hc'
        simpa only [show (fun x : ℝ => x * Real.cos x - Real.sin x) 0 = 0 by
          norm_num] using ht
    · exact tendsto_nhdsWithin_of_tendsto_nhds <| by
        have h := (hasDerivAt_pow 3 (0 : ℝ)).continuousAt
        have ht : Tendsto (fun x : ℝ => x ^ 3) (nhds 0)
            (nhds ((fun x : ℝ => x ^ 3) 0)) := h
        simpa only [show (fun x : ℝ => x ^ 3) 0 = 0 by norm_num] using ht
    · have hsinc : Tendsto Real.sinc (𝓝[≠] 0) (𝓝 1) :=
        tendsto_nhdsWithin_of_tendsto_nhds (by
          have h : ContinuousAt Real.sinc 0 := Real.continuous_sinc.continuousAt
          rw [← Real.sinc_zero]
          exact h)
      have ht := hsinc.neg.div_const 3
      have heq : (fun x : ℝ => -(x * Real.sin x) / (3 * x ^ 2))
          =ᶠ[nhdsWithin (0 : ℝ) {0}ᶜ]
          fun x => -Real.sinc x / 3 := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        rw [Real.sinc_of_ne_zero hx]
        field_simp
      simpa only [neg_div] using ht.congr' heq.symm
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [sincD1]
  have hx0 : x ≠ 0 := hx
  field_simp [hx0]

/-- The total first derivative has the correctly totalized second derivative
at every real point. -/
theorem hasDerivAt_sincD1Total (x : ℝ) :
    HasDerivAt sincD1Total (sincD2Total x) x := by
  by_cases hx : x = 0
  · subst x
    rw [hasDerivAt_iff_tendsto_slope, sincD2Total_zero]
    apply tendsto_sincD1_div_zero.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_fun_def_field]
    change sincD1 x / x = (sincD1Total x - sincD1Total 0) / (x - 0)
    rw [sincD1Total_zero, sincD1Total_eq hx]
    ring
  · have h := hasDerivAt_sincD1 hx
    rw [sincD2Total_eq hx]
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact sincD1Total_eq hy

/-- Total first derivative of the current closed kernel. -/
def closedKernelD1Total (x : ℝ) : ℝ :=
  ∑ j : Fin 7, coefficient j * Real.pi *
    (sincD1Total (plusArgument j x) - sincD1Total (minusArgument j x)) / 2

/-- Total second derivative of the current closed kernel. -/
def closedKernelD2Total (x : ℝ) : ℝ :=
  ∑ j : Fin 7, coefficient j * Real.pi ^ 2 *
    (sincD2Total (minusArgument j x) + sincD2Total (plusArgument j x)) / 2

/-- Total first derivative of the squared normalized current kernel. -/
def closedWeightD1Total (x : ℝ) : ℝ :=
  2 * closedKernel x * closedKernelD1Total x / closedKernel 0 ^ 2

/-- Total second derivative of the squared normalized current kernel. -/
def closedWeightD2Total (x : ℝ) : ℝ :=
  2 * (closedKernelD1Total x ^ 2 + closedKernel x * closedKernelD2Total x) /
    closedKernel 0 ^ 2

theorem hasDerivAt_closedKernel_total (x : ℝ) :
    HasDerivAt closedKernel (closedKernelD1Total x) x := by
  unfold closedKernel closedKernelD1Total
  apply HasDerivAt.fun_sum
  intro j _
  have hm := (hasDerivAt_sinc_total (minusArgument j x)).comp x
    (hasDerivAt_minusArgument j x)
  have hp := (hasDerivAt_sinc_total (plusArgument j x)).comp x
    (hasDerivAt_plusArgument j x)
  have h := ((hm.add hp).div_const 2).const_mul (coefficient j)
  have hd : coefficient j *
      ((sincD1Total (minusArgument j x) * -Real.pi +
        sincD1Total (plusArgument j x) * Real.pi) / 2) =
      coefficient j * Real.pi *
        (sincD1Total (plusArgument j x) -
          sincD1Total (minusArgument j x)) / 2 := by ring
  have h' := h.congr_deriv hd
  apply h'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by
    simp only [Function.comp_apply, Pi.add_apply, minusArgument, plusArgument]
    ring

theorem hasDerivAt_closedKernelD1Total (x : ℝ) :
    HasDerivAt closedKernelD1Total (closedKernelD2Total x) x := by
  unfold closedKernelD1Total closedKernelD2Total
  apply HasDerivAt.fun_sum
  intro j _
  have hm := (hasDerivAt_sincD1Total (minusArgument j x)).comp x
    (hasDerivAt_minusArgument j x)
  have hp := (hasDerivAt_sincD1Total (plusArgument j x)).comp x
    (hasDerivAt_plusArgument j x)
  have h := ((hp.sub hm).const_mul (coefficient j * Real.pi)).div_const 2
  simpa only [Function.comp_apply, Pi.sub_apply] using
    (h.congr_deriv (by ring))

theorem hasDerivAt_closedWeight_total (x : ℝ) :
    HasDerivAt (fun y => (closedKernel y / closedKernel 0) ^ 2)
      (closedWeightD1Total x) x := by
  have h := ((hasDerivAt_closedKernel_total x).div_const
    (closedKernel 0)).pow 2
  apply h.congr_deriv
  unfold closedWeightD1Total
  ring

theorem hasDerivAt_closedWeightD1Total (x : ℝ) :
    HasDerivAt closedWeightD1Total (closedWeightD2Total x) x := by
  have hk := hasDerivAt_closedKernel_total x
  have hk1 := hasDerivAt_closedKernelD1Total x
  have h := (((hk.const_mul 2).mul hk1).div_const (closedKernel 0 ^ 2))
  change HasDerivAt
    (fun y => 2 * closedKernel y * closedKernelD1Total y / closedKernel 0 ^ 2)
    (closedWeightD2Total x) x
  apply h.congr_deriv
  unfold closedWeightD2Total
  ring

/-- Table-ready all-point semantic statement: `closedWeightD2Total` is the
second derivative of the exact current-window weight at every real point. -/
theorem hasDerivAt_currentWeightD1 (x : ℝ) :
    HasDerivAt closedWeightD1Total (closedWeightD2Total x) x :=
  hasDerivAt_closedWeightD1Total x

theorem hasDerivAt_currentWeight (x : ℝ) :
    HasDerivAt CurrentWindow.weight (closedWeightD1Total x) x := by
  apply (hasDerivAt_closedWeight_total x).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y =>
    CurrentKernelFormula.weight_eq_closedKernel y

theorem deriv_currentWeight (x : ℝ) :
    deriv CurrentWindow.weight x = closedWeightD1Total x :=
  (hasDerivAt_currentWeight x).deriv

/-- Pointwise identity between the semantic first derivative and Lean's
actual derivative function. -/
theorem deriv_currentWeight_fun :
    deriv CurrentWindow.weight = closedWeightD1Total := by
  funext x
  exact deriv_currentWeight x

/-- Table-ready second-derivative identity, valid even when one of the sinc
arguments is its removable zero. -/
theorem deriv2_currentWeight (x : ℝ) :
    deriv (deriv CurrentWindow.weight) x = closedWeightD2Total x := by
  rw [deriv_currentWeight_fun]
  exact (hasDerivAt_currentWeightD1 x).deriv

theorem closedWeightD1Total_eq_closedWeightD1 (x : ℝ)
    (hneMinus : ∀ j : Fin 7, minusArgument j x ≠ 0)
    (hnePlus : ∀ j : Fin 7, plusArgument j x ≠ 0) :
    closedWeightD1Total x =
      2 * closedKernel x * closedKernelD1 x / closedKernel 0 ^ 2 := by
  have h1 : closedKernelD1Total x = closedKernelD1 x := by
    unfold closedKernelD1Total closedKernelD1
    apply Finset.sum_congr rfl
    intro j _
    rw [sincD1Total_eq (hnePlus j), sincD1Total_eq (hneMinus j)]
  simp [closedWeightD1Total, h1]

theorem closedWeightD2Total_eq_closedWeightD2 (x : ℝ)
    (hneMinus : ∀ j : Fin 7, minusArgument j x ≠ 0)
    (hnePlus : ∀ j : Fin 7, plusArgument j x ≠ 0) :
    closedWeightD2Total x = closedWeightD2 x := by
  have h1 : closedKernelD1Total x = closedKernelD1 x := by
    unfold closedKernelD1Total closedKernelD1
    apply Finset.sum_congr rfl
    intro j _
    rw [sincD1Total_eq (hnePlus j), sincD1Total_eq (hneMinus j)]
  have h2 : closedKernelD2Total x = closedKernelD2 x := by
    unfold closedKernelD2Total closedKernelD2
    apply Finset.sum_congr rfl
    intro j _
    rw [sincD2Total_eq (hneMinus j), sincD2Total_eq (hnePlus j)]
  simp [closedWeightD2Total, closedWeightD2, h1, h2]

end Zeta23Ext.CurrentKernelTotalDerivatives

end
