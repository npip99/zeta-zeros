/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Kernel-checked Taylor enclosures for transcendental table generation

This module begins replacing the Arb trust boundary with exact rational
inequalities.  The main theorem gives a reusable Taylor enclosure for sine on
a nonnegative interval.  Its proof uses Mathlib's Lagrange/mean-value Taylor
theorem and the kernel-checked fact that every iterated derivative of sine has
absolute value at most one.

The order-seven specialization has a completely rational polynomial and
remainder.  It is directly usable by an interval evaluator after rational
range reduction; no floating-point or external interval library occurs here.
-/

noncomputable section

open Set

namespace Zeta23Ext.TranscendentalBounds

/-- Taylor polynomial for sine expressed through derivatives at zero.  The
closed form is used first because it supports every order uniformly. -/
def sinTaylorWithin (order : ℕ) (upper x : ℝ) : ℝ :=
  taylorWithinEval Real.sin order (Set.Icc 0 upper) 0 x

/-- General, kernel-checked sine remainder on `[0, upper]`.

The bound is deliberately the slightly looser `x^(n+1)/n!` supplied by
`taylor_mean_remainder_bound`; it has the advantage of needing only the
uniform derivative bound `1` and works at every order.
-/
theorem abs_sin_sub_sinTaylorWithin_le
    (order : ℕ) {upper x : ℝ} (hupper : 0 < upper)
    (hx : x ∈ Set.Icc (0 : ℝ) upper) :
    |Real.sin x - sinTaylorWithin order upper x| ≤
      x ^ (order + 1) / order.factorial := by
  have hbound := taylor_mean_remainder_bound
    (f := Real.sin) (a := (0 : ℝ)) (b := upper) (C := (1 : ℝ))
    (x := x) (n := order) hupper.le Real.contDiff_sin.contDiffOn hx
    (fun y hy => by
      rw [Real.iteratedDerivWithin_sin_Icc (order + 1) hupper hy]
      simpa only [Real.norm_eq_abs] using
        Real.abs_iteratedDeriv_sin_le_one (order + 1) y)
  simpa [sinTaylorWithin, Real.norm_eq_abs] using hbound

/-- The explicit rational degree-seven sine polynomial. -/
def sinTaylor7 (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040

/-- Evaluation of the abstract Taylor polynomial at order seven reduces to
the explicit rational polynomial. -/
lemma sinTaylorWithin_seven {upper x : ℝ} (hupper : 0 < upper) :
    sinTaylorWithin 7 upper x = sinTaylor7 x := by
  have hderiv : ∀ k : ℕ,
      iteratedDerivWithin k Real.sin (Set.Icc (0 : ℝ) upper) 0 =
        iteratedDeriv k Real.sin 0 := by
    intro k
    exact Real.iteratedDerivWithin_sin_Icc k hupper ⟨le_rfl, hupper.le⟩
  rw [sinTaylorWithin, taylor_within_apply]
  simp_rw [hderiv]
  norm_num [sinTaylor7, Real.iteratedDeriv_even_sin, Real.iteratedDeriv_odd_sin,
    Finset.sum_range_succ]
  ring

/-- A fully rational, order-seven enclosure for sine on a nonnegative
interval. -/
theorem abs_sin_sub_sinTaylor7_le {upper x : ℝ} (hupper : 0 < upper)
    (hx : x ∈ Set.Icc (0 : ℝ) upper) :
    |Real.sin x - sinTaylor7 x| ≤ x ^ 8 / 5040 := by
  rw [← sinTaylorWithin_seven hupper]
  have h := abs_sin_sub_sinTaylorWithin_le 7 hupper hx
  norm_num at h ⊢
  exact h

/-- Two-sided rational enclosure extracted from the absolute-error theorem. -/
theorem sin_mem_taylor7_interval {upper x : ℝ} (hupper : 0 < upper)
    (hx : x ∈ Set.Icc (0 : ℝ) upper) :
    sinTaylor7 x - x ^ 8 / 5040 ≤ Real.sin x ∧
      Real.sin x ≤ sinTaylor7 x + x ^ 8 / 5040 := by
  obtain ⟨hupper', hlower⟩ :=
    abs_sub_le_iff.mp (abs_sin_sub_sinTaylor7_le hupper hx)
  constructor <;> linarith

/-- Odd reflection extends the positive-interval enclosure to negative
arguments without another transcendental estimate. -/
theorem sin_neg_mem_taylor7_interval {upper x : ℝ} (hupper : 0 < upper)
    (hx : x ∈ Set.Icc (0 : ℝ) upper) :
    -(sinTaylor7 x + x ^ 8 / 5040) ≤ Real.sin (-x) ∧
      Real.sin (-x) ≤ -(sinTaylor7 x - x ^ 8 / 5040) := by
  obtain ⟨hlower, hupper'⟩ := sin_mem_taylor7_interval hupper hx
  rw [Real.sin_neg]
  constructor <;> linarith

/-- Rational enclosure on a whole cell around a nonnegative rational center.

After a range-reduction step places the center `c` in `[0, upper]`, a caller
only needs a rational radius bound `|x-c| ≤ radius`.  The result uses the
Taylor error at the center plus the global `1`-Lipschitz bound for sine.  This
form is especially convenient for grid-table generation because every term on
the right is rational when `c` and `radius` are rational.
-/
theorem abs_sin_sub_taylor7_center_le {upper c x radius : ℝ}
    (hupper : 0 < upper) (hc : c ∈ Set.Icc (0 : ℝ) upper)
    (hxc : |x - c| ≤ radius) :
    |Real.sin x - sinTaylor7 c| ≤ radius + c ^ 8 / 5040 := by
  calc
    |Real.sin x - sinTaylor7 c| ≤
        |Real.sin x - Real.sin c| + |Real.sin c - sinTaylor7 c| := by
      exact abs_sub_le _ _ _
    _ ≤ |x - c| + c ^ 8 / 5040 := by
      exact add_le_add (Real.abs_sin_sub_sin_le x c)
        (abs_sin_sub_sinTaylor7_le hupper hc)
    _ ≤ radius + c ^ 8 / 5040 := by linarith

/-- Two-sided version of `abs_sin_sub_taylor7_center_le`. -/
theorem sin_mem_taylor7_center_interval {upper c x radius : ℝ}
    (hupper : 0 < upper) (hc : c ∈ Set.Icc (0 : ℝ) upper)
    (hxc : |x - c| ≤ radius) :
    sinTaylor7 c - (radius + c ^ 8 / 5040) ≤ Real.sin x ∧
      Real.sin x ≤ sinTaylor7 c + (radius + c ^ 8 / 5040) := by
  obtain ⟨hupper', hlower⟩ :=
    abs_sub_le_iff.mp (abs_sin_sub_taylor7_center_le hupper hc hxc)
  constructor <;> linarith

/-- Concrete rational regression: at `x = 1/2`, the enclosure is decided
entirely by the kernel after applying the proved Taylor theorem. -/
theorem sin_one_half_bounds :
    (18407 : ℝ) / 38400 ≤ Real.sin (1 / 2) ∧
      Real.sin (1 / 2) ≤ (30967 : ℝ) / 64512 := by
  have h := sin_mem_taylor7_interval (upper := (1 : ℝ)) (x := (1 : ℝ) / 2)
    one_pos (by constructor <;> norm_num)
  norm_num [sinTaylor7] at h ⊢
  constructor <;> linarith [h.1, h.2]

end Zeta23Ext.TranscendentalBounds
