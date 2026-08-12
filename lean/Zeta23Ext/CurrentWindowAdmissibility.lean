/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowInterface
import Zeta23Ext.CurrentAnalyticBridge
import Zeta23.XiPrime.QuarticWindow.ModWindow
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Admissibility of the current cosine window

This file turns the finite core facts in `CurrentWindow.WindowCertificate` into
the analytic `AdmWindow` input used by the upstream arbitrary-window API.  The
calculus and all four derivative-integral estimates are kernel checked.  The
only input is the finite certificate's pointwise lower/upper and monotonicity
statements (plus its unused `H` endpoint statement).
-/

noncomputable section

open Real Set Filter Topology
open scoped BigOperators

namespace Zeta23Ext.CurrentWindowAdmissibility

open Zeta23
open Zeta23.XiPrime
open Zeta23Ext.CurrentWindow

/-- A global first-derivative envelope for the exact cosine polynomial. -/
def slopeBound : ℝ :=
  ∑ j : Fin 7, |coefficient j| * |frequency j|

/-- A global second-derivative envelope for the exact cosine polynomial. -/
def curvatureBound : ℝ :=
  ∑ j : Fin 7, |coefficient j| * |frequency j| ^ 2

/-- Constants used by the generic modulated-window theorem.  The deliberately
generous second term comes from differentiating a square root while using only
the certified lower bound `window ≥ 3/4`. -/
def factorA : ℝ := slopeBound
def factorB : ℝ := curvatureBound + 2 * slopeBound ^ 2

lemma slopeBound_nonneg : 0 ≤ slopeBound := by
  unfold slopeBound
  positivity

lemma curvatureBound_nonneg : 0 ≤ curvatureBound := by
  unfold curvatureBound
  positivity

lemma factorA_nonneg : 0 ≤ factorA := slopeBound_nonneg

lemma factorB_nonneg : 0 ≤ factorB := by
  unfold factorB
  nlinarith [curvatureBound_nonneg, sq_nonneg slopeBound]

/-- The exact cosine polynomial is smooth to every finite order. -/
lemma window_contDiff : ContDiff ℝ 2 window := by
  unfold window
  fun_prop

lemma hasDerivAt_window (s : ℝ) :
    HasDerivAt window
      (∑ j : Fin 7, -(coefficient j * frequency j * Real.sin (frequency j * s))) s := by
  unfold window
  apply HasDerivAt.fun_sum
  intro j _
  have harg : HasDerivAt (fun x : ℝ => frequency j * x) (frequency j) s := by
    simpa using (hasDerivAt_id s).const_mul (frequency j)
  have hterm := ((Real.hasDerivAt_cos (frequency j * s)).comp s harg).const_mul
    (coefficient j)
  have hterm' : HasDerivAt (fun y => coefficient j * (Real.cos ∘ (frequency j * ·)) y)
      (-(coefficient j * frequency j * Real.sin (frequency j * s))) s :=
    hterm.congr_deriv (by ring)
  simpa only [Function.comp_apply] using hterm'

lemma deriv_window (s : ℝ) :
    deriv window s =
      ∑ j : Fin 7, -(coefficient j * frequency j * Real.sin (frequency j * s)) :=
  (hasDerivAt_window s).deriv

lemma hasDerivAt_deriv_window (s : ℝ) :
    HasDerivAt (deriv window)
      (∑ j : Fin 7, -(coefficient j * frequency j ^ 2 * Real.cos (frequency j * s))) s := by
  have heq : deriv window = fun x =>
      ∑ j : Fin 7, -(coefficient j * frequency j * Real.sin (frequency j * x)) :=
    funext deriv_window
  rw [heq]
  apply HasDerivAt.fun_sum
  intro j _
  have harg : HasDerivAt (fun x : ℝ => frequency j * x) (frequency j) s := by
    simpa using (hasDerivAt_id s).const_mul (frequency j)
  have hterm := ((Real.hasDerivAt_sin (frequency j * s)).comp s harg).const_mul
    (-(coefficient j * frequency j))
  have hterm' : HasDerivAt
      (fun y => -(coefficient j * frequency j) * (Real.sin ∘ (frequency j * ·)) y)
      (-(coefficient j * frequency j ^ 2 * Real.cos (frequency j * s))) s :=
    hterm.congr_deriv (by ring)
  apply hterm'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by simp only [Function.comp_apply]; ring

lemma deriv2_window (s : ℝ) :
    deriv (deriv window) s =
      ∑ j : Fin 7, -(coefficient j * frequency j ^ 2 * Real.cos (frequency j * s)) :=
  (hasDerivAt_deriv_window s).deriv

lemma abs_deriv_window_le (s : ℝ) : |deriv window s| ≤ slopeBound := by
  rw [deriv_window]
  calc
    |∑ j : Fin 7, -(coefficient j * frequency j * Real.sin (frequency j * s))|
        ≤ ∑ j : Fin 7, |-(coefficient j * frequency j * Real.sin (frequency j * s))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 7, |coefficient j| * |frequency j| := by
      gcongr with j
      rw [abs_neg, abs_mul, abs_mul]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (Real.abs_sin_le_one _)
    _ = slopeBound := rfl

lemma abs_deriv2_window_le (s : ℝ) : |deriv (deriv window) s| ≤ curvatureBound := by
  rw [deriv2_window]
  calc
    |∑ j : Fin 7, -(coefficient j * frequency j ^ 2 * Real.cos (frequency j * s))|
        ≤ ∑ j : Fin 7, |-(coefficient j * frequency j ^ 2 * Real.cos (frequency j * s))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 7, |coefficient j| * |frequency j| ^ 2 := by
      gcongr with j
      rw [abs_neg, abs_mul, abs_mul, abs_pow]
      exact mul_le_of_le_one_right
        (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (Real.abs_cos_le_one _)
    _ = curvatureBound := rfl

/-- The square-root factor in the actual `phiV` definition, in physical
`u`-coordinates. -/
def factor (L : ℝ) (u : ℝ) : ℝ :=
  Real.sqrt (max 0 (window (u / L)))

lemma factor_even (L u : ℝ) : factor L (-u) = factor L u := by
  simp only [factor, neg_div, window_even]

lemma factor_nonneg (L u : ℝ) : 0 ≤ factor L u := Real.sqrt_nonneg _

private lemma core_scaled {L u : ℝ} (hL : 0 < L) (hu : |u| ≤ L / 2) :
    u / L ∈ Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
  rw [mem_Icc]
  obtain ⟨hu₁, hu₂⟩ := abs_le.mp hu
  constructor
  · rw [le_div_iff₀ hL]
    linarith
  · rw [div_le_iff₀ hL]
    linarith

lemma factor_le_one (hcert : WindowCertificate) {L u : ℝ} (hL : 0 < L)
    (hu : |u| ≤ L / 2) : factor L u ≤ 1 := by
  have hs := core_scaled hL hu
  have hv0 : 0 ≤ window (u / L) := le_trans (by norm_num) (hcert.lower _ hs)
  rw [factor, max_eq_right hv0, ← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (hcert.upper _ hs)

lemma factor_antitone (hcert : WindowCertificate) {L : ℝ} (hL : 0 < L) :
    AntitoneOn (factor L) (Icc 0 (L / 2)) := by
  intro x hx y hy hxy
  unfold factor
  apply Real.sqrt_le_sqrt
  apply max_le_max le_rfl
  apply hcert.nonincreasing
  · exact ⟨div_nonneg hx.1 hL.le, (div_le_iff₀ hL).2 (by linarith [hx.2])⟩
  · exact ⟨div_nonneg hy.1 hL.le, (div_le_iff₀ hL).2 (by linarith [hy.2])⟩
  · exact div_le_div_of_nonneg_right hxy hL.le

private lemma core_subset_positive (hcert : WindowCertificate) :
    Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) ⊆ {s : ℝ | 0 < window s} := by
  intro s hs
  exact lt_of_lt_of_le (by norm_num) (hcert.lower s hs)

private lemma interval_subset_thickening {ε : ℝ} (hε : 0 < ε) :
    Ioo (-((1 : ℝ) / 2 + ε / 2)) ((1 : ℝ) / 2 + ε / 2) ⊆
      Metric.thickening ε (Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) := by
  intro s hs
  rw [Metric.mem_thickening_iff]
  by_cases hlo : s < -(1 : ℝ) / 2
  · refine ⟨-(1 : ℝ) / 2, by constructor <;> norm_num, ?_⟩
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith [hs.1]
  · by_cases hhi : (1 : ℝ) / 2 < s
    · refine ⟨(1 : ℝ) / 2, by constructor <;> norm_num, ?_⟩
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith [hs.2]
    · refine ⟨s, ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩, ?_⟩
      simp [hε]

/-- Positivity on the certified compact core, plus continuity of the explicit
cosine polynomial, supplies the neighbourhood needed to smooth the `max` in
the definition of `factor`. -/
lemma factor_smooth (hcert : WindowCertificate) {L : ℝ} (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧
      ContDiffOn ℝ 2 (factor L) (Ioo (-(L / 2 + δ)) (L / 2 + δ)) := by
  let U : Set ℝ := {s : ℝ | 0 < window s}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_window
  obtain ⟨ε, hε, hthick⟩ :=
    (isCompact_Icc.exists_thickening_subset_open hUopen (core_subset_positive hcert))
  refine ⟨L * ε / 2, by positivity, ?_⟩
  let q : ℝ → ℝ := fun u => window (u / L)
  have hq : ContDiff ℝ 2 q := by
    dsimp [q]
    exact window_contDiff.comp (contDiff_id.div_const L)
  have hpos : ∀ u ∈ Ioo (-(L / 2 + L * ε / 2)) (L / 2 + L * ε / 2), 0 < q u := by
    intro u hu
    apply hthick
    apply interval_subset_thickening hε
    constructor
    · rw [show -(L / 2 + L * ε / 2) = L * (-((1 : ℝ) / 2 + ε / 2)) by ring] at hu
      exact (lt_div_iff₀ hL).2 (by nlinarith [hu.1])
    · rw [show L / 2 + L * ε / 2 = L * ((1 : ℝ) / 2 + ε / 2) by ring] at hu
      exact (div_lt_iff₀ hL).2 (by nlinarith [hu.2])
  have hsqrt : ContDiffOn ℝ 2 (fun u => Real.sqrt (q u))
      (Ioo (-(L / 2 + L * ε / 2)) (L / 2 + L * ε / 2)) :=
    hq.contDiffOn.sqrt (fun u hu => (hpos u hu).ne')
  exact hsqrt.congr fun u hu => by
    rw [factor, max_eq_right (hpos u hu).le]

private lemma q_hasDerivAt {L u : ℝ} (hL : 0 < L) :
    HasDerivAt (fun x => window (x / L)) (deriv window (u / L) / L) u := by
  have hw : HasDerivAt window (deriv window (u / L)) (u / L) :=
    (window_contDiff.differentiable (by norm_num) (u / L)).hasDerivAt
  have h := hw.comp u ((hasDerivAt_id u).div_const L)
  have h' : HasDerivAt (window ∘ fun x => id x / L)
      (deriv window (u / L) / L) u := h.congr_deriv (by ring)
  apply h'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by simp [Function.comp_def, mul_comm]

private lemma q1_hasDerivAt {L u : ℝ} (hL : 0 < L) :
    HasDerivAt (fun x => deriv window (x / L) / L)
      (deriv (deriv window) (u / L) / L ^ 2) u := by
  have hw : HasDerivAt (deriv window) (deriv (deriv window) (u / L)) (u / L) :=
    ((window_contDiff.deriv' (n := 1)).differentiable (by norm_num) (u / L)).hasDerivAt
  have h := (hw.comp u ((hasDerivAt_id u).div_const L)).div_const L
  have h' : HasDerivAt (fun x => ((deriv window) ∘ fun y => id y / L) x / L)
      (deriv (deriv window) (u / L) / L ^ 2) u := h.congr_deriv (by ring)
  apply h'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by simp [Function.comp_def, mul_comm]

private lemma factor_hasDerivAt (hcert : WindowCertificate) {L u : ℝ} (hL : 0 < L)
    (hu : |u| ≤ L / 2) :
    HasDerivAt (factor L)
      ((deriv window (u / L) / L) / (2 * Real.sqrt (window (u / L)))) u := by
  have hs := core_scaled hL hu
  have hv : 0 < window (u / L) := lt_of_lt_of_le (by norm_num) (hcert.lower _ hs)
  have heq : factor L =ᶠ[nhds u] fun x => Real.sqrt (window (x / L)) := by
    have hev : ∀ᶠ x in nhds u, 0 < window (x / L) :=
      (continuous_window.comp (continuous_id.div_const L)).continuousAt.preimage_mem_nhds
        (isOpen_Ioi.mem_nhds hv)
    filter_upwards [hev] with x hx
    rw [factor, max_eq_right hx.le]
  exact (((q_hasDerivAt hL).sqrt hv.ne').congr_of_eventuallyEq heq)

private lemma sqrt_core_ge_half (hcert : WindowCertificate) {L u : ℝ} (hL : 0 < L)
    (hu : |u| ≤ L / 2) : (1 : ℝ) / 2 ≤ Real.sqrt (window (u / L)) := by
  have hs := core_scaled hL hu
  have hv : 0 ≤ window (u / L) := le_trans (by norm_num) (hcert.lower _ hs)
  rw [Real.le_sqrt (by norm_num) hv]
  nlinarith [hcert.lower _ hs]

lemma abs_deriv_factor_le (hcert : WindowCertificate) {L u : ℝ} (hL : 0 < L)
    (hu : |u| ≤ L / 2) : |deriv (factor L) u| ≤ factorA / L := by
  rw [(factor_hasDerivAt hcert hL hu).deriv, abs_div, abs_div]
  have hsqrt := sqrt_core_ge_half hcert hL hu
  have hden : 1 ≤ |2 * Real.sqrt (window (u / L))| := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]
    linarith
  have hnum := abs_deriv_window_le (u / L)
  have hL0 : 0 ≤ |L| := abs_nonneg L
  rw [abs_of_pos hL]
  calc
    |deriv window (u / L)| / L / |2 * Real.sqrt (window (u / L))|
        ≤ |deriv window (u / L)| / L / 1 := by gcongr
    _ = |deriv window (u / L)| / L := by ring
    _ ≤ slopeBound / L := (div_le_div_iff_of_pos_right hL).2 hnum
    _ = factorA / L := rfl

private lemma deriv_factor_eventually (hcert : WindowCertificate) {L u : ℝ} (hL : 0 < L)
    (hu : |u| ≤ L / 2) :
    deriv (factor L) =ᶠ[nhds u] fun x =>
      (deriv window (x / L) / L) / (2 * Real.sqrt (window (x / L))) := by
  have hs := core_scaled hL hu
  have hv : 0 < window (u / L) := lt_of_lt_of_le (by norm_num) (hcert.lower _ hs)
  have hev : ∀ᶠ x in nhds u, 0 < window (x / L) :=
    (continuous_window.comp (continuous_id.div_const L)).continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds hv)
  filter_upwards [hev] with x hx
  have heq : factor L =ᶠ[nhds x] fun y => Real.sqrt (window (y / L)) := by
    have hevy : ∀ᶠ y in nhds x, 0 < window (y / L) :=
      (continuous_window.comp (continuous_id.div_const L)).continuousAt.preimage_mem_nhds
        (isOpen_Ioi.mem_nhds hx)
    filter_upwards [hevy] with y hy
    rw [factor, max_eq_right hy.le]
  exact (((q_hasDerivAt hL).sqrt hx.ne').congr_of_eventuallyEq heq).deriv

private lemma deriv2_factor_formula (hcert : WindowCertificate) {L u : ℝ} (hL : 0 < L)
    (hu : |u| ≤ L / 2) :
    deriv (deriv (factor L)) u =
      (deriv (deriv window) (u / L) / L ^ 2) /
          (2 * Real.sqrt (window (u / L)))
        - (deriv window (u / L) / L) ^ 2 /
          (4 * Real.sqrt (window (u / L)) ^ 3) := by
  have hs := core_scaled hL hu
  have hv : 0 < window (u / L) := lt_of_lt_of_le (by norm_num) (hcert.lower _ hs)
  let q := fun x : ℝ => window (x / L)
  let q1 := fun x : ℝ => deriv window (x / L) / L
  have hq : HasDerivAt q (deriv window (u / L) / L) u := q_hasDerivAt hL
  have hq1 : HasDerivAt q1 (deriv (deriv window) (u / L) / L ^ 2) u := q1_hasDerivAt hL
  have hsqrt : HasDerivAt (fun x => Real.sqrt (q x))
      ((deriv window (u / L) / L) / (2 * Real.sqrt (window (u / L)))) u :=
    hq.sqrt hv.ne'
  have hden : HasDerivAt (fun x => 2 * Real.sqrt (q x))
      (2 * ((deriv window (u / L) / L) / (2 * Real.sqrt (window (u / L))))) u :=
    hsqrt.const_mul 2
  have hquot' : HasDerivAt (fun x : ℝ =>
      (deriv window (x / L) / L) / (2 * Real.sqrt (window (x / L))))
      ((deriv (deriv window) (u / L) / L ^ 2 * (2 * Real.sqrt (window (u / L))) -
        (deriv window (u / L) / L) *
          (2 * ((deriv window (u / L) / L) / (2 * Real.sqrt (window (u / L)))))) /
        (2 * Real.sqrt (window (u / L))) ^ 2) u := by
    exact hq1.div hden (by positivity : 2 * Real.sqrt (q u) ≠ 0)
  have heq : deriv (deriv (factor L)) u =
      deriv (fun x =>
        (deriv window (x / L) / L) / (2 * Real.sqrt (window (x / L)))) u :=
    (deriv_factor_eventually hcert hL hu).deriv_eq
  rw [heq, hquot'.deriv]
  field_simp
  ring

lemma abs_deriv2_factor_le (hcert : WindowCertificate) {L u : ℝ} (hL : 0 < L)
    (hu : |u| ≤ L / 2) : |deriv (deriv (factor L)) u| ≤ factorB / L ^ 2 := by
  rw [deriv2_factor_formula hcert hL hu]
  have hsqrt := sqrt_core_ge_half hcert hL hu
  have hsqrt0 : 0 ≤ Real.sqrt (window (u / L)) := Real.sqrt_nonneg _
  have hd1 := abs_deriv_window_le (u / L)
  have hd2 := abs_deriv2_window_le (u / L)
  have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
  have hden1 : 1 ≤ |2 * Real.sqrt (window (u / L))| := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hsqrt0)]
    linarith
  have hden2 : (1 : ℝ) / 2 ≤ |4 * Real.sqrt (window (u / L)) ^ 3| := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (pow_nonneg hsqrt0 _))]
    nlinarith [sq_nonneg (Real.sqrt (window (u / L)) - 1 / 2)]
  have ht1 :
      |deriv (deriv window) (u / L) / L ^ 2 /
          (2 * Real.sqrt (window (u / L)))|
        ≤ curvatureBound / L ^ 2 := by
    rw [abs_div, abs_div, abs_of_pos hL2]
    calc
      |deriv (deriv window) (u / L)| / L ^ 2 /
          |2 * Real.sqrt (window (u / L))|
        ≤ |deriv (deriv window) (u / L)| / L ^ 2 / 1 := by
          gcongr
      _ = |deriv (deriv window) (u / L)| / L ^ 2 := by ring
      _ ≤ curvatureBound / L ^ 2 := (div_le_div_iff_of_pos_right hL2).2 hd2
  have hsq : |deriv window (u / L) / L| ^ 2 ≤ slopeBound ^ 2 / L ^ 2 := by
    rw [abs_div, abs_of_pos hL, div_pow]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) hd1 2) hL2.le
  have ht2 :
      |(deriv window (u / L) / L) ^ 2 /
          (4 * Real.sqrt (window (u / L)) ^ 3)|
        ≤ 2 * slopeBound ^ 2 / L ^ 2 := by
    rw [abs_div, abs_pow]
    calc
      |deriv window (u / L) / L| ^ 2 /
          |4 * Real.sqrt (window (u / L)) ^ 3|
        ≤ |deriv window (u / L) / L| ^ 2 / ((1 : ℝ) / 2) := by
          exact div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden2
      _ = 2 * |deriv window (u / L) / L| ^ 2 := by ring
      _ ≤ 2 * (slopeBound ^ 2 / L ^ 2) := by gcongr
      _ = 2 * slopeBound ^ 2 / L ^ 2 := by ring
  calc
    |deriv (deriv window) (u / L) / L ^ 2 / (2 * Real.sqrt (window (u / L)))
        - (deriv window (u / L) / L) ^ 2 /
          (4 * Real.sqrt (window (u / L)) ^ 3)|
      ≤ |deriv (deriv window) (u / L) / L ^ 2 /
          (2 * Real.sqrt (window (u / L)))|
        + |(deriv window (u / L) / L) ^ 2 /
          (4 * Real.sqrt (window (u / L)) ^ 3)| := abs_sub _ _
    _ ≤ curvatureBound / L ^ 2 + 2 * slopeBound ^ 2 / L ^ 2 := add_le_add ht1 ht2
    _ = factorB / L ^ 2 := by unfold factorB; ring

/-- The exact square-root cosine factor satisfies the upstream structural and
pointwise analytic interface. -/
theorem modFactor_current (hcert : WindowCertificate) {L : ℝ} (hL : 0 < L) :
    ModFactor (factor L) L factorA factorB where
  A_nonneg := factorA_nonneg
  B_nonneg := factorB_nonneg
  even := factor_even L
  nonneg := factor_nonneg L
  le_one := fun u hu => factor_le_one hcert hL hu
  antitone := factor_antitone hcert hL
  smooth := factor_smooth hcert hL
  deriv_le := fun u hu => abs_deriv_factor_le hcert hL hu
  deriv2_le := fun u hu => abs_deriv2_factor_le hcert hL hu

/-- The current `phiV` window is definitionally the generic modulated taper. -/
lemma phiV_current_eq (P : Params) (T : ℝ) :
    P.phiV window T = phiM (factor (P.L T)) P.ϱ (P.L T) P.w := rfl

/-- A concrete, fully analytic admissibility theorem for the current window.
All support, regularity, and L¹ derivative fields are supplied by the upstream
generic theorem from the proved `ModFactor` witness. -/
theorem admWindow_current {P : Params} (hP : P.Valid) (hcert : WindowCertificate)
    {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    AdmWindow (P.phiV window T) (P.L T) P.w (cMod P.ϱ factorA factorB) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  rw [phiV_current_eq]
  exact admWindow_phiM (modFactor_current hcert hL) hP.taper hP.one_le_w h8

/-- The requested bridge record.  Its constant is explicit and independent of
`T`; no analytic admissibility premise remains. -/
def currentWindowAdmissibility {P : Params} (hP : P.Valid)
    (hcert : WindowCertificate) :
    Zeta23Ext.CurrentAnalyticBridge.CurrentWindowAdmissibility P where
  cW := cMod P.ϱ factorA factorB
  admissible := fun _T h8 => admWindow_current hP hcert h8

end Zeta23Ext.CurrentWindowAdmissibility

end
