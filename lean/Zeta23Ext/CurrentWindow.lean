/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.WeightedAggregation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exact current-window data

This module records the perturbed cosine window used by the `0.673195`
certificate.  It deliberately does not claim that the external Arb search has
been replayed by Lean: `LocalCertificate` is the exact proposition that such a
replay must prove.
-/

noncomputable section

open scoped BigOperators

namespace Zeta23Ext.CurrentWindow

/-- Exact rational coefficient of the `j`th cosine term. -/
def coefficient (j : Fin 7) : ℝ :=
  match (j : ℕ) with
  | 0 => 1
  | 1 => 3322500 / 1000000000
  | 2 => -7609135 / 1000000000
  | 3 => 1190194 / 1000000000
  | 4 => -731476 / 1000000000
  | 5 => -1680572 / 1000000000
  | 6 => 1141360 / 1000000000
  | _ => 0

/-- Frequencies `sqrt 2, 2*pi, 4*pi, ..., 12*pi`. -/
def frequency : Fin 7 → ℝ
  | ⟨0, _⟩ => Real.sqrt 2
  | ⟨j + 1, _⟩ => 2 * Real.pi * (j + 1)

/-- The exact even cosine window on `[-1/2,1/2]`. -/
def window (s : ℝ) : ℝ :=
  ∑ j : Fin 7, coefficient j * Real.cos (frequency j * s)

/-- Its (unnormalized) cosine autocorrelation kernel. -/
def kernel (x : ℝ) : ℝ :=
  ∫ s in (-(1:ℝ)/2)..(1/2), window s * Real.cos (2 * Real.pi * x * s)

/-- The normalized kernel used by the local certificate. -/
def normalizedKernel (x : ℝ) : ℝ := kernel x / kernel 0

/-- The nonnegative pair potential in the weighted seven-point functional. -/
def weight (x : ℝ) : ℝ := normalizedKernel x ^ 2

lemma window_even (s : ℝ) : window (-s) = window s := by
  unfold window
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [show frequency j * -s = -(frequency j * s) by ring, Real.cos_neg]

lemma kernel_even (x : ℝ) : kernel (-x) = kernel x := by
  unfold kernel
  refine intervalIntegral.integral_congr ?_
  intro s _
  change window s * Real.cos (2 * Real.pi * -x * s) =
    window s * Real.cos (2 * Real.pi * x * s)
  congr 1
  rw [show 2 * Real.pi * -x * s = -(2 * Real.pi * x * s) by ring, Real.cos_neg]

lemma normalizedKernel_even (x : ℝ) : normalizedKernel (-x) = normalizedKernel x := by
  rw [normalizedKernel, normalizedKernel, kernel_even]

lemma weight_nonneg (x : ℝ) : 0 ≤ weight x := by
  unfold weight
  positivity

lemma weight_even (x : ℝ) : weight (-x) = weight x := by
  rw [weight, weight, normalizedKernel_even]

/-- Exact statement discharged by the external `509/100000` interval
certificate.  It remains visibly a proposition, not an axiom or theorem. -/
def LocalCertificate : Prop :=
  ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) →
    Weighted.beta ≤ Weighted.F6 weight g

end Zeta23Ext.CurrentWindow
