/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds

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

/-! ## Cosine enclosures

The window range and derivative certificates also need cosine evaluations.
The following parallel development keeps their future interval evaluator on
the same exact-rational footing as the sine table above.
-/

/-- Taylor polynomial for cosine expressed through derivatives at zero. -/
def cosTaylorWithin (order : ℕ) (upper x : ℝ) : ℝ :=
  taylorWithinEval Real.cos order (Set.Icc 0 upper) 0 x

/-- General, kernel-checked cosine remainder on `[0, upper]`. -/
theorem abs_cos_sub_cosTaylorWithin_le
    (order : ℕ) {upper x : ℝ} (hupper : 0 < upper)
    (hx : x ∈ Set.Icc (0 : ℝ) upper) :
    |Real.cos x - cosTaylorWithin order upper x| ≤
      x ^ (order + 1) / order.factorial := by
  have hbound := taylor_mean_remainder_bound
    (f := Real.cos) (a := (0 : ℝ)) (b := upper) (C := (1 : ℝ))
    (x := x) (n := order) hupper.le Real.contDiff_cos.contDiffOn hx
    (fun y hy => by
      rw [Real.iteratedDerivWithin_cos_Icc (order + 1) hupper hy]
      simpa only [Real.norm_eq_abs] using
        Real.abs_iteratedDeriv_cos_le_one (order + 1) y)
  simpa [cosTaylorWithin, Real.norm_eq_abs] using hbound

/-- The explicit rational degree-eight cosine polynomial. -/
def cosTaylor8 (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320

/-- The abstract order-eight Taylor polynomial is the explicit rational one. -/
lemma cosTaylorWithin_eight {upper x : ℝ} (hupper : 0 < upper) :
    cosTaylorWithin 8 upper x = cosTaylor8 x := by
  have hderiv : ∀ k : ℕ,
      iteratedDerivWithin k Real.cos (Set.Icc (0 : ℝ) upper) 0 =
        iteratedDeriv k Real.cos 0 := by
    intro k
    exact Real.iteratedDerivWithin_cos_Icc k hupper ⟨le_rfl, hupper.le⟩
  rw [cosTaylorWithin, taylor_within_apply]
  simp_rw [hderiv]
  norm_num [cosTaylor8, Real.iteratedDeriv_even_cos,
    Real.iteratedDeriv_odd_cos, Finset.sum_range_succ]
  ring

/-- Fully rational order-eight enclosure for cosine on a nonnegative interval. -/
theorem abs_cos_sub_cosTaylor8_le {upper x : ℝ} (hupper : 0 < upper)
    (hx : x ∈ Set.Icc (0 : ℝ) upper) :
    |Real.cos x - cosTaylor8 x| ≤ x ^ 9 / 40320 := by
  rw [← cosTaylorWithin_eight hupper]
  have h := abs_cos_sub_cosTaylorWithin_le 8 hupper hx
  norm_num at h ⊢
  exact h

/-- Two-sided rational cosine enclosure. -/
theorem cos_mem_taylor8_interval {upper x : ℝ} (hupper : 0 < upper)
    (hx : x ∈ Set.Icc (0 : ℝ) upper) :
    cosTaylor8 x - x ^ 9 / 40320 ≤ Real.cos x ∧
      Real.cos x ≤ cosTaylor8 x + x ^ 9 / 40320 := by
  obtain ⟨hupper', hlower⟩ :=
    abs_sub_le_iff.mp (abs_cos_sub_cosTaylor8_le hupper hx)
  constructor <;> linarith

/-- Rational enclosure on a cell around a nonnegative center. -/
theorem abs_cos_sub_taylor8_center_le {upper c x radius : ℝ}
    (hupper : 0 < upper) (hc : c ∈ Set.Icc (0 : ℝ) upper)
    (hxc : |x - c| ≤ radius) :
    |Real.cos x - cosTaylor8 c| ≤ radius + c ^ 9 / 40320 := by
  calc
    |Real.cos x - cosTaylor8 c| ≤
        |Real.cos x - Real.cos c| + |Real.cos c - cosTaylor8 c| := by
      exact abs_sub_le _ _ _
    _ ≤ |x - c| + c ^ 9 / 40320 := by
      exact add_le_add (Real.abs_cos_sub_cos_le x c)
        (abs_cos_sub_cosTaylor8_le hupper hc)
    _ ≤ radius + c ^ 9 / 40320 := by linarith

/-- Concrete exact-rational regression for cosine at `1/2`. -/
theorem cos_one_half_bounds :
    (351 : ℝ) / 400 ≤ Real.cos (1 / 2) ∧
      Real.cos (1 / 2) ≤ (439 : ℝ) / 500 := by
  have h := cos_mem_taylor8_interval (upper := (1 : ℝ)) (x := (1 : ℝ) / 2)
    one_pos (by constructor <;> norm_num)
  norm_num [cosTaylor8] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-! ## Algebraic square-root enclosures -/

/-- Rational square bounds turn directly into a square-root enclosure.  This
is the exact bridge needed when interval evaluation reaches the profile
`sqrt (max (window s) 0)`. -/
theorem sqrt_mem_interval {x lower upper : ℝ}
    (hx : 0 ≤ x) (_hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (hlowerSq : lower ^ 2 ≤ x) (hupperSq : x ≤ upper ^ 2) :
    lower ≤ Real.sqrt x ∧ Real.sqrt x ≤ upper := by
  have hsqrt := Real.sq_sqrt hx
  have hsqrt_nonneg := Real.sqrt_nonneg x
  constructor <;> nlinarith

/-- Concrete dyadic-table regression enclosure for `sqrt 2`. -/
theorem sqrt_two_bounds :
    (707 : ℝ) / 500 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (283 : ℝ) / 200 := by
  apply sqrt_mem_interval (x := (2 : ℝ)) <;> norm_num

/-- Mathlib's kernel-checked twenty-decimal enclosure for `pi`, restated in
the exact rational form used by a dyadic interval generator. -/
theorem pi_rational_bounds :
    (314159265358979323846 : ℝ) / 10 ^ 20 < Real.pi ∧
      Real.pi < (314159265358979323847 : ℝ) / 10 ^ 20 := by
  constructor
  · convert Real.pi_gt_d20 using 1
    norm_num
  · convert Real.pi_lt_d20 using 1
    norm_num

/-! ## Removable sinc enclosures -/

/-- Degree-six polynomial obtained by dividing the odd sine polynomial by
its argument. -/
def sincTaylor6 (x : ℝ) : ℝ :=
  1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040

lemma sinTaylor7_eq_mul_sincTaylor6 (x : ℝ) :
    sinTaylor7 x = x * sincTaylor6 x := by
  unfold sinTaylor7 sincTaylor6
  ring

lemma sincTaylor6_neg (x : ℝ) : sincTaylor6 (-x) = sincTaylor6 x := by
  unfold sincTaylor6
  ring

/-- Rational sinc enclosure on a nonnegative interval, including the
removable point `x=0`. -/
theorem abs_sinc_sub_sincTaylor6_le {upper x : ℝ} (hupper : 0 < upper)
    (hx : x ∈ Set.Icc (0 : ℝ) upper) :
    |Real.sinc x - sincTaylor6 x| ≤ x ^ 7 / 5040 := by
  by_cases hx0 : x = 0
  · subst x
    norm_num [Real.sinc_zero, sincTaylor6]
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    rw [Real.sinc_of_ne_zero hx0]
    have hsinc : sincTaylor6 x = sinTaylor7 x / x := by
      rw [sinTaylor7_eq_mul_sincTaylor6]
      field_simp [hx0]
    rw [hsinc]
    have heq : |Real.sin x / x - sinTaylor7 x / x| =
        |Real.sin x - sinTaylor7 x| / x := by
      rw [← sub_div, abs_div, abs_of_pos hxpos]
    rw [heq, div_le_iff₀ hxpos]
    calc
      |Real.sin x - sinTaylor7 x| ≤ x ^ 8 / 5040 :=
        abs_sin_sub_sinTaylor7_le hupper hx
      _ = (x ^ 7 / 5040) * x := by ring

/-- Negative arguments reduce exactly to the nonnegative sinc enclosure. -/
theorem abs_sinc_neg_sub_sincTaylor6_le {upper x : ℝ} (hupper : 0 < upper)
    (hx : x ∈ Set.Icc (0 : ℝ) upper) :
    |Real.sinc (-x) - sincTaylor6 (-x)| ≤ x ^ 7 / 5040 := by
  simpa [Real.sinc_neg, sincTaylor6_neg] using
    abs_sinc_sub_sincTaylor6_le hupper hx

end Zeta23Ext.TranscendentalBounds
