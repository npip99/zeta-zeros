/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowAdmissibility
import Zeta23Ext.CurrentKernelFormula
import Zeta23Ext.TranscendentalBounds

/-!
# A finite proof-producing certificate for the current window

This module narrows `CurrentWindow.WindowCertificate`.  Instead of trusting
quantified range and monotonicity assertions, a producer supplies finitely
many derivative values at cell centres.  Exact global curvature and jerk
bounds, proved from the seven cosine terms, extend those centre inequalities
over the cells.  Only the endpoint inequality and the scalar `H` inequality
remain transcendental numeric leaves.
-/

noncomputable section

open Real Set Filter Topology
open scoped BigOperators

namespace Zeta23Ext.CurrentWindowFiniteCertificate

open CurrentWindow
open CurrentWindowAdmissibility

/-- Global envelope for the third derivative of the seven-term cosine sum. -/
def jerkBound : ℝ :=
  ∑ j : Fin 7, |coefficient j| * |frequency j| ^ 3

lemma jerkBound_nonneg : 0 ≤ jerkBound := by
  unfold jerkBound
  positivity

lemma hasDerivAt_deriv2_window (s : ℝ) :
    HasDerivAt (deriv (deriv window))
      (∑ j : Fin 7,
        coefficient j * frequency j ^ 3 * Real.sin (frequency j * s)) s := by
  have heq : deriv (deriv window) = fun x =>
      ∑ j : Fin 7,
        -(coefficient j * frequency j ^ 2 * Real.cos (frequency j * x)) :=
    funext deriv2_window
  rw [heq]
  apply HasDerivAt.fun_sum
  intro j _
  have harg : HasDerivAt (fun x : ℝ => frequency j * x) (frequency j) s := by
    simpa using (hasDerivAt_id s).const_mul (frequency j)
  have hterm := ((Real.hasDerivAt_cos (frequency j * s)).comp s harg).const_mul
    (-(coefficient j * frequency j ^ 2))
  have hterm' : HasDerivAt
      (fun y => -(coefficient j * frequency j ^ 2) *
        (Real.cos ∘ (frequency j * ·)) y)
      (coefficient j * frequency j ^ 3 * Real.sin (frequency j * s)) s :=
    hterm.congr_deriv (by ring)
  apply hterm'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by simp only [Function.comp_apply]; ring

lemma deriv3_window (s : ℝ) :
    deriv (deriv (deriv window)) s =
      ∑ j : Fin 7,
        coefficient j * frequency j ^ 3 * Real.sin (frequency j * s) :=
  (hasDerivAt_deriv2_window s).deriv

lemma abs_deriv3_window_le (s : ℝ) :
    |deriv (deriv (deriv window)) s| ≤ jerkBound := by
  rw [deriv3_window]
  calc
    |∑ j : Fin 7, coefficient j * frequency j ^ 3 * Real.sin (frequency j * s)|
        ≤ ∑ j : Fin 7,
          |coefficient j * frequency j ^ 3 * Real.sin (frequency j * s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 7, |coefficient j| * |frequency j| ^ 3 := by
      gcongr with j
      rw [abs_mul, abs_mul, abs_pow]
      exact mul_le_of_le_one_right
        (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
        (Real.abs_sin_le_one _)
    _ = jerkBound := rfl

lemma deriv_window_zero : deriv window 0 = 0 := by
  rw [deriv_window]
  simp

lemma deriv_lipschitz (x y : ℝ) :
    |deriv window y - deriv window x| ≤ curvatureBound * |y - x| := by
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (f := deriv window) (x := x) (y := y) (C := curvatureBound)
    (fun z _ => ((window_contDiff.deriv' (n := 1)).differentiable
      (by norm_num) z))
    (fun z _ => by simpa [Real.norm_eq_abs] using abs_deriv2_window_le z)
    (Set.mem_univ x) (Set.mem_univ y)
  simpa only [Real.norm_eq_abs] using h

lemma deriv2_lipschitz (x y : ℝ) :
    |deriv (deriv window) y - deriv (deriv window) x| ≤ jerkBound * |y - x| := by
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (f := deriv (deriv window)) (x := x) (y := y) (C := jerkBound)
    (fun z _ => (hasDerivAt_deriv2_window z).differentiableAt)
    (fun z _ => by simpa [Real.norm_eq_abs] using abs_deriv3_window_le z)
    (Set.mem_univ x) (Set.mem_univ y)
  simpa only [Real.norm_eq_abs] using h

/-- A symmetric cell, represented by its centre and radius. -/
structure DerivativeCell where
  center : ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius

def DerivativeCell.Covers (cell : DerivativeCell) (s : ℝ) : Prop :=
  |s - cell.center| ≤ cell.radius

/-- Finite monotonicity certificate.

The origin cell is handled with `v''`: its centre is exactly zero, so the
proved identity `v'(0)=0` removes the interval dependency at the junction.
Every later cell uses one centre evaluation of `v'`. -/
structure MonotonicityTable (n : ℕ) where
  originRadius : ℝ
  originRadius_pos : 0 < originRadius
  originRadius_le_half : originRadius ≤ 1 / 2
  originSecondUpper :
    deriv (deriv window) 0 + jerkBound * originRadius ≤ 0
  cells : Fin n → DerivativeCell
  centerUpper : ∀ i, deriv window (cells i).center +
    curvatureBound * (cells i).radius ≤ 0
  cover : ∀ s ∈ Icc originRadius (1 / 2), ∃ i, (cells i).Covers s

private lemma second_nonpos_on_origin {n : ℕ} (table : MonotonicityTable n)
    {s : ℝ} (hs : s ∈ Icc 0 table.originRadius) :
    deriv (deriv window) s ≤ 0 := by
  have hlip := deriv2_lipschitz 0 s
  have habs : |s - 0| ≤ table.originRadius := by
    simpa [abs_of_nonneg hs.1] using hs.2
  have hdiff : deriv (deriv window) s - deriv (deriv window) 0 ≤
      jerkBound * table.originRadius := by
    calc
      deriv (deriv window) s - deriv (deriv window) 0
          ≤ |deriv (deriv window) s - deriv (deriv window) 0| := le_abs_self _
      _ ≤ jerkBound * |s - 0| := hlip
      _ ≤ jerkBound * table.originRadius :=
        mul_le_mul_of_nonneg_left habs jerkBound_nonneg
  linarith [table.originSecondUpper]

lemma derivative_nonpos_of_table {n : ℕ} (table : MonotonicityTable n)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) : deriv window s ≤ 0 := by
  rcases le_or_gt s table.originRadius with hnear | hfar
  · have hanti : AntitoneOn (deriv window) (Icc 0 table.originRadius) :=
      antitoneOn_of_deriv_nonpos (D := Icc 0 table.originRadius) (convex_Icc _ _)
        ((window_contDiff.deriv' (n := 1)).continuous.continuousOn)
        ((window_contDiff.deriv' (n := 1)).differentiable
          (by norm_num)).differentiableOn
        (fun x hx => second_nonpos_on_origin table (interior_subset hx))
    have := hanti ⟨le_rfl, table.originRadius_pos.le⟩ ⟨hs.1, hnear⟩ hs.1
    rw [deriv_window_zero] at this
    exact this
  · obtain ⟨i, hi⟩ := table.cover s ⟨hfar.le, hs.2⟩
    have hlip := deriv_lipschitz (table.cells i).center s
    have hdiff : deriv window s - deriv window (table.cells i).center ≤
        curvatureBound * (table.cells i).radius := by
      calc
        deriv window s - deriv window (table.cells i).center
            ≤ |deriv window s - deriv window (table.cells i).center| := le_abs_self _
        _ ≤ curvatureBound * |s - (table.cells i).center| := hlip
        _ ≤ curvatureBound * (table.cells i).radius :=
          mul_le_mul_of_nonneg_left hi curvatureBound_nonneg
    linarith [table.centerUpper i]

lemma window_antitone_of_table {n : ℕ} (table : MonotonicityTable n) :
    AntitoneOn window (Icc (0 : ℝ) (1 / 2)) := by
  apply antitoneOn_of_deriv_nonpos (D := Icc (0 : ℝ) (1 / 2)) (convex_Icc _ _)
    continuous_window.continuousOn
    (window_contDiff.differentiable (by norm_num)).differentiableOn
  intro s hs
  exact derivative_nonpos_of_table table
    (interior_subset hs)

/-- The upper endpoint is an exact rational check because every cosine is
evaluated at zero. -/
lemma window_zero_le_one : window 0 ≤ 1 := by
  norm_num [window, coefficient, frequency, Fin.sum_univ_succ]

lemma cos_sqrt_two_half_lower :
    (7601 : ℝ) / 10000 ≤ Real.cos (Real.sqrt 2 / 2) := by
  have hr := TranscendentalBounds.sqrt_two_bounds
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : Real.sqrt 2 / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · linarith [hr.2]
  have hc := (TranscendentalBounds.cos_mem_taylor8_interval
    (upper := (1 : ℝ)) (x := Real.sqrt 2 / 2) one_pos hx).1
  unfold TranscendentalBounds.cosTaylor8 at hc
  have hr8 : (Real.sqrt 2) ^ 8 = 16 := by
    calc
      (Real.sqrt 2) ^ 8 = ((Real.sqrt 2) ^ 2) ^ 4 := by ring
      _ = 16 := by rw [hr2]; norm_num
  have hr9 : (Real.sqrt 2) ^ 9 ≤ 16 * ((283 : ℝ) / 200) := by
    calc
      (Real.sqrt 2) ^ 9 = (Real.sqrt 2) ^ 8 * Real.sqrt 2 := by ring
      _ ≤ 16 * ((283 : ℝ) / 200) := by rw [hr8]; gcongr; exact hr.2
  nlinarith [hr2, hr8, hr9]

/-- The lower endpoint is kernel checked: all six periodic terms reduce to
`cos (j*pi)=(-1)^j`, and the sole algebraic-frequency term uses Taylor. -/
lemma window_half_lower : 3 / 4 ≤ window (1 / 2) := by
  have hc := cos_sqrt_two_half_lower
  have hterm : ∀ j : Fin 7,
      coefficient j * Real.cos (frequency j * (1 / 2)) =
        match (j : ℕ) with
        | 0 => Real.cos (Real.sqrt 2 / 2)
        | 1 => -(3322500 / 1000000000 : ℝ)
        | 2 => -(7609135 / 1000000000 : ℝ)
        | 3 => -(1190194 / 1000000000 : ℝ)
        | 4 => -(731476 / 1000000000 : ℝ)
        | 5 => (1680572 / 1000000000 : ℝ)
        | 6 => (1141360 / 1000000000 : ℝ)
        | _ => 0 := by
    intro j
    fin_cases j <;> norm_num [coefficient, frequency] <;> ring_nf <;>
      try norm_num [Real.cos_nat_mul_pi, mul_comm]
    case «2» => rw [show Real.pi * 2 = (2 : ℤ) * Real.pi by norm_num; ring,
      Real.cos_int_mul_pi]; norm_num
    case «3» => rw [show Real.pi * 3 = (3 : ℤ) * Real.pi by norm_num; ring,
      Real.cos_int_mul_pi]; norm_num
    case «4» => rw [show Real.pi * 4 = (4 : ℤ) * Real.pi by norm_num; ring,
      Real.cos_int_mul_pi]; norm_num
    case «5» => rw [show Real.pi * 5 = (5 : ℤ) * Real.pi by norm_num; ring,
      Real.cos_int_mul_pi]; norm_num
    case «6» => rw [show Real.pi * 6 = (6 : ℤ) * Real.pi by norm_num; ring,
      Real.cos_int_mul_pi]; norm_num
  unfold window
  simp_rw [hterm]
  norm_num [Fin.sum_univ_succ]
  linarith

/-- The mass integral already has a proved closed sinc form through the
zero-frequency kernel. -/
lemma windowMass_closed :
    windowMass window = CurrentKernelFormula.closedKernel 0 := by
  rw [← kernel_zero_eq_mass, CurrentKernelFormula.kernel_eq_closedKernel]

/-- Exact finite double-sum formula for the square-mass term in `H`. -/
def closedWindowSquareMass : ℝ :=
  ∑ i : Fin 7, ∑ j : Fin 7, coefficient i * coefficient j *
    (Real.sinc ((frequency i - frequency j) / 2) +
      Real.sinc ((frequency i + frequency j) / 2)) / 2

lemma windowSquareMass_closed :
    windowSquareMass window = closedWindowSquareMass := by
  unfold windowSquareMass window closedWindowSquareMass
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [show (fun x : ℝ => coefficient i * Real.cos (frequency i * x) *
          (coefficient j * Real.cos (frequency j * x))) =
          fun x => (coefficient i * coefficient j) *
            (Real.cos (frequency i * x) * Real.cos (frequency j * x)) by
            funext x; ring]
      rw [intervalIntegral.integral_const_mul,
        CurrentKernelFormula.integral_cos_mul_cos]
      ring
    · intro j _
      exact (by fun_prop : Continuous (fun x : ℝ =>
        coefficient i * Real.cos (frequency i * x) *
          (coefficient j * Real.cos (frequency j * x)))).intervalIntegrable _ _
  · intro i _
    exact (by fun_prop : Continuous (fun s : ℝ =>
      ∑ j : Fin 7, coefficient i * Real.cos (frequency i * s) *
        (coefficient j * Real.cos (frequency j * s)))).intervalIntegrable _ _

/-
The following direct antiderivative development is retained as design work,
but is not compiled yet: interval-orientation bookkeeping still needs to be
finished before it can be promoted to the trusted interface.

/-! ## Closed form for the distance mass -/

/-- The verifier's cosine/cosine integral abbreviation. -/
def cosCosIntegral (a b : ℝ) : ℝ :=
  (Real.sinc ((a - b) / 2) + Real.sinc ((a + b) / 2)) / 2

/-- Closed form for `∫∫ |s-t| cos(a s) cos(b t)`.  This spelling uses
`b` for the frequency integrated in the inner variable; swapping `a,b`
gives the algebraically equal spelling in `h0_cert.py`. -/
def absKernelIntegral (a b : ℝ) : ℝ :=
  (Real.sin (b / 2) / b + 2 * Real.cos (b / 2) / b ^ 2) * Real.sinc (a / 2) -
    2 / b ^ 2 * cosCosIntegral a b

private lemma inner_abs_cos {b s : ℝ} (hb : b ≠ 0)
    (hs : s ∈ Icc (-(1 : ℝ) / 2) (1 / 2)) :
    (∫ t in (-(1 : ℝ) / 2)..(1 / 2), |s - t| * Real.cos (b * t)) =
      Real.sin (b / 2) / b + 2 * Real.cos (b / 2) / b ^ 2 -
        2 * Real.cos (b * s) / b ^ 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (f := fun t : ℝ => |s - t| * Real.cos (b * t))
    (by exact (by fun_prop : Continuous (fun t : ℝ =>
      |s - t| * Real.cos (b * t))).intervalIntegrable _ _)
    (by exact (by fun_prop : Continuous (fun t : ℝ =>
      |s - t| * Real.cos (b * t))).intervalIntegrable _ _)]
  have hleft : (∫ t in (-(1 : ℝ) / 2)..s, |s - t| * Real.cos (b * t)) =
      (∫ t in (-(1 : ℝ) / 2)..s, (s - t) * Real.cos (b * t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [abs_of_nonneg]
    linarith [ht.2]
  have hright : (∫ t in s..(1 / 2), |s - t| * Real.cos (b * t)) =
      (∫ t in s..(1 / 2), (t - s) * Real.cos (b * t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [abs_of_nonpos]
    linarith [ht.1]
  rw [hleft, hright]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => (s - t) * Real.sin (b * t) / b - Real.cos (b * t) / b ^ 2)]
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => (t - s) * Real.sin (b * t) / b + Real.cos (b * t) / b ^ 2)]
    · rw [show b * (-(1 : ℝ) / 2) = -(b / 2) by ring,
        Real.sin_neg, Real.cos_neg]
      field_simp [hb]
      ring
    · intro t _
      have hsin := (Real.hasDerivAt_sin (b * t)).comp t
        (hasDerivAt_const_mul (x := t) b)
      have hcos := (Real.hasDerivAt_cos (b * t)).comp t
        (hasDerivAt_const_mul (x := t) b)
      convert ((((hasDerivAt_id t).sub_const s).mul hsin).div_const b).add
        (hcos.div_const (b ^ 2)) using 1 <;> field_simp [hb] <;> ring
    · fun_prop
  · intro t _
    have hsin := (Real.hasDerivAt_sin (b * t)).comp t
      (hasDerivAt_const_mul (x := t) b)
    have hcos := (Real.hasDerivAt_cos (b * t)).comp t
      (hasDerivAt_const_mul (x := t) b)
    convert ((((hasDerivAt_const t s).sub (hasDerivAt_id t)).mul hsin).div_const b).sub
      (hcos.div_const (b ^ 2)) using 1 <;> field_simp [hb] <;> ring
  · fun_prop

theorem integral_abs_cos_cos {a b : ℝ} (hb : b ≠ 0) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
      ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
        |s - t| * Real.cos (a * s) * Real.cos (b * t)) =
      absKernelIntegral a b := by
  have hinner : ∀ s ∈ Icc (-(1 : ℝ) / 2) (1 / 2),
      (∫ t in (-(1 : ℝ) / 2)..(1 / 2),
        |s - t| * Real.cos (a * s) * Real.cos (b * t)) =
      Real.cos (a * s) *
        (Real.sin (b / 2) / b + 2 * Real.cos (b / 2) / b ^ 2 -
          2 * Real.cos (b * s) / b ^ 2) := by
    intro s hs
    rw [show (fun t : ℝ => |s - t| * Real.cos (a * s) * Real.cos (b * t)) =
        fun t => Real.cos (a * s) * (|s - t| * Real.cos (b * t)) by
          funext t; ring,
      intervalIntegral.integral_const_mul, inner_abs_cos hb hs]
  apply Eq.trans (intervalIntegral.integral_congr (fun s hs => hinner s (by
    simpa [uIcc_of_le (by norm_num : (-(1 : ℝ) / 2) ≤ 1 / 2)] using hs)))
  rw [show (fun s : ℝ => Real.cos (a * s) *
      (Real.sin (b / 2) / b + 2 * Real.cos (b / 2) / b ^ 2 -
        2 * Real.cos (b * s) / b ^ 2)) =
      fun s => (Real.sin (b / 2) / b + 2 * Real.cos (b / 2) / b ^ 2) *
          Real.cos (a * s) -
        (2 / b ^ 2) * (Real.cos (a * s) * Real.cos (b * s)) by
      funext s; ring]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, CurrentKernelFormula.integral_cos_linear,
    CurrentKernelFormula.integral_cos_mul_cos]
  · rfl
  · exact (by fun_prop : Continuous (fun s : ℝ =>
      (Real.sin (b / 2) / b + 2 * Real.cos (b / 2) / b ^ 2) *
        Real.cos (a * s))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun s : ℝ =>
      (2 / b ^ 2) * (Real.cos (a * s) * Real.cos (b * s)))).intervalIntegrable _ _

/-- Entire finite expression used for the distance term in `H`. -/
def closedWindowDistanceMass : ℝ :=
  ∑ i : Fin 7, ∑ j : Fin 7,
    coefficient i * coefficient j * absKernelIntegral (frequency i) (frequency j)

lemma frequency_ne_zero (j : Fin 7) : frequency j ≠ 0 := by
  fin_cases j <;> simp [frequency, Real.sqrt_ne_zero'] <;> positivity

lemma windowDistanceMass_closed :
    windowDistanceMass window = closedWindowDistanceMass := by
  unfold windowDistanceMass window closedWindowDistanceMass
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [show (fun s : ℝ => ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
          |s - t| * (coefficient i * Real.cos (frequency i * s)) *
            (coefficient j * Real.cos (frequency j * t))) =
          fun s => (coefficient i * coefficient j) *
            (∫ t in (-(1 : ℝ) / 2)..(1 / 2),
              |s - t| * Real.cos (frequency i * s) *
                Real.cos (frequency j * t)) by
          funext s
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t _
          ring]
      rw [intervalIntegral.integral_const_mul,
        integral_abs_cos_cos (frequency_ne_zero j)]
    · intro j _
      fun_prop
  · intro i _
    fun_prop

/-- The exact finite scalar whose lower bound is the `H` certificate. -/
def closedH : ℝ :=
  2 - (closedWindowSquareMass + closedWindowDistanceMass) /
    CurrentKernelFormula.closedKernel 0 ^ 2

lemma H_eq_closedH : H window = closedH := by
  unfold H c1 closedH
  rw [windowMass_closed, windowSquareMass_closed, windowDistanceMass_closed]
  field_simp <;> ring
-/

/-- Narrow numeric leaves from which the original broad certificate follows.
`HLower` is one scalar functional inequality; `windowMass_closed` and
`windowSquareMass_closed`
remove two of its three analytic integrals, while the distance-mass closed
formula remains future work.  All quantified range/monotonicity fields are
derived from the finite table. -/
structure NumericCertificate (n : ℕ) where
  monotonicity : MonotonicityTable n
  HLower : Hcert ≤ H window

theorem NumericCertificate.toWindowCertificate {n : ℕ}
    (cert : NumericCertificate n) : WindowCertificate where
  lower := by
    intro s hs
    have habs : |s| ∈ Icc (0 : ℝ) (1 / 2) := by
      exact ⟨abs_nonneg _, abs_le.2 ⟨by linarith [hs.1], hs.2⟩⟩
    have hanti := window_antitone_of_table cert.monotonicity
      habs (right_mem_Icc.mpr (by norm_num)) habs.2
    have heq : window |s| = window s := by
      rcases le_or_gt 0 s with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, window_even]
    rw [heq] at hanti
    exact window_half_lower.trans hanti
  upper := by
    intro s hs
    have habs : |s| ∈ Icc (0 : ℝ) (1 / 2) :=
      ⟨abs_nonneg _, abs_le.2 ⟨by linarith [hs.1], hs.2⟩⟩
    have hanti := window_antitone_of_table cert.monotonicity
      (left_mem_Icc.mpr (by norm_num)) habs (abs_nonneg _)
    have heq : window |s| = window s := by
      rcases le_or_gt 0 s with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, window_even]
    rw [heq] at hanti
    exact hanti.trans window_zero_le_one
  even := window_even
  nonincreasing := window_antitone_of_table cert.monotonicity
  H_lower := cert.HLower

end Zeta23Ext.CurrentWindowFiniteCertificate

end
