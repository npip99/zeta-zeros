/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentAssembly
import Zeta23.XiPrime.QuarticWindow.ZeroSide

/-!
# Honest analytic reuse for the current window

This module records the part of the arbitrary-window analytic input that can
actually be reused from the pinned `Zeta23` tree.

There are three deliberately separate results.

* `currentWindowZeroSide` reuses the generic modulated-window zero-side
  theorem from `Zeta23.XiPrime.QuarticWindow.ZeroSide`.  Its only genuinely
  window-specific analytic premise is an `AdmWindow` witness for the current
  profile.  The lower mass bound, Poisson identity, block input, and tail
  package are then derived rather than assumed.
* `PairwiseGramData.guardedBlockApprox` turns a compact-uniform, pairwise
  squared-energy estimate into the aggregate block inequality consumed by
  `CurrentAssembly`.  Thus the aggregate inequality is not an independent
  analytic hypothesis.
* `MomentData.stabilitySeam` derives the current defect-enhanced stability
  seam from the existing rank--trace theorem and primitive count/trace/
  Frobenius bounds.

What is *not* discharged here is important.  The old extension's
`gram_entry_close` is specialized to the Montgomery--Taylor kernel
`kkernelL`, and its `Final.stability_zeta_at` uses that same window and its
old constants.  Neither theorem implies compact-uniform convergence to
`CurrentWindow.kernel`.  The current-window `AdmWindow` witness and the
pairwise squared-energy estimate below therefore remain explicit primitives;
no old Montgomery--Taylor theorem is silently relabelled as a current-window
result.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Filter Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentAnalyticBridge

open Zeta23
open Zeta23Ext
open Zeta23Ext.Stability

/-! ## Reuse of the pinned generic modulated-window zero side -/

/-- Pointwise comparison between the current modulated window and the base
ramp.  On the core it is exactly the certified lower bound `v >= 3/4`; off
the core the base ramp vanishes. -/
lemma current_phiV_sq_ge {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (u : ℝ) :
    3 / 4 * P.phi T u ^ 2 ≤ P.phiV CurrentWindow.window T u ^ 2 := by
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  rw [Params.phiV_eq, mul_pow, ← Params.phi_eq]
  rcases le_or_gt (P.L T / 2) |u| with hu | hu
  · rw [Params.phi_eq_zero hP hu]
    simp
  · have hcore : u / P.L T ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
      rw [Set.mem_Icc]
      have habs := (abs_lt.mp hu)
      constructor
      · rw [le_div_iff₀ hL]
        linarith
      · rw [div_le_iff₀ hL]
        linarith
    have hv := hcert.lower (u / P.L T) hcore
    rw [Real.sq_sqrt (le_max_left _ _), max_eq_right (by linarith)]
    exact mul_le_mul_of_nonneg_right hv (sq_nonneg _)

/-- The `a >= 1/2` premise required by the pinned generic zero-side theorem
follows from current-window positivity and `8w <= L`.  Admissibility is used
only for integrability of the modulated window. -/
theorem current_a_half {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {cW T : ℝ}
    (h8 : 8 * P.w ≤ P.L T)
    (hW : AdmWindow (P.phiV CurrentWindow.window T) (P.L T) P.w cW) :
    1 / 2 ≤ (P.atV CurrentWindow.window T).a T := by
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have h2 : 2 * P.w ≤ P.L T := by linarith
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hbase : 1 - 2 * P.w / P.L T ≤ P.a T :=
    (Taper.one_sub_le_bConst hP.taper hw0 h2).trans
      (Taper.bConst_le_aConst hP.taper hw0 h2)
  have hwL : 2 * P.w / P.L T ≤ 1 / 4 := by
    rw [div_le_iff₀ hL]
    linarith
  have hint : MeasureTheory.Integrable
      (fun u => P.phiV CurrentWindow.window T u ^ 2) :=
    hW.integrable_pow two_pos
  have hint' : MeasureTheory.Integrable (fun u => 3 / 4 * P.phi T u ^ 2) :=
    ((Params.phi_continuous hP (by linarith)).fun_pow 2 |>.integrable_of_hasCompactSupport
      ((Params.phi_hasCompactSupport hP).comp_left
        (g := fun t => t ^ 2) (by norm_num))).const_mul _
  have hcmp : 3 / 4 * ∫ u, P.phi T u ^ 2 ≤
      ∫ u, P.phiV CurrentWindow.window T u ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono hint' hint
      (current_phiV_sq_ge hP hcert h8)
  have ha : P.a T = (P.L T)⁻¹ * ∫ u, P.phi T u ^ 2 := rfl
  rw [Params.atV_a T hP CurrentWindow.window_even]
  unfold AdmWindow.av
  rw [ha] at hbase
  have hLi : 0 < (P.L T)⁻¹ := inv_pos.mpr hL
  calc
    (1 : ℝ) / 2 ≤ 3 / 4 * (1 - 2 * P.w / P.L T) := by nlinarith
    _ ≤ 3 / 4 * ((P.L T)⁻¹ * ∫ u, P.phi T u ^ 2) := by gcongr
    _ = (P.L T)⁻¹ * (3 / 4 * ∫ u, P.phi T u ^ 2) := by ring
    _ ≤ (P.L T)⁻¹ * ∫ u, P.phiV CurrentWindow.window T u ^ 2 :=
      mul_le_mul_of_nonneg_left hcmp hLi.le

/-- The smallest upstream-window premise retained by this module.  It asks
for the actual `AdmWindow` statement, not merely informal `C²` prose. -/
structure CurrentWindowAdmissibility (P : Params) where
  cW : ℝ
  admissible : ∀ T : ℝ, 8 * P.w ≤ P.L T →
    AdmWindow (P.phiV CurrentWindow.window T) (P.L T) P.w cW

/-- Genuine reuse from pinned upstream: current-window admissibility implies
the entire generic zero-side package (Poisson, block, tail, and mass facts).
This theorem does not supply the prime-side moments or a Gram-kernel limit. -/
theorem currentWindowZeroSide {Z : ZeroConfig} {P : Params}
    (hP : P.Valid) (hR : RiemannVonMangoldt Z)
    (hcert : CurrentWindow.WindowCertificate)
    (hA : CurrentWindowAdmissibility P) :
    XiPrime.WindowZeroSide Z P (P.atV CurrentWindow.window) := by
  refine XiPrime.windowZeroSide_atV_of hP CurrentWindow.window_even
    hA.admissible ?_ Z hR
  filter_upwards [Params.eventually_w8 hP] with T h8
  exact current_a_half hP hcert h8 (hA.admissible T h8)

/-! ## Pairwise compact Gram control implies the guarded block input -/

/-- Uniform pairwise error charged to one block.  There are `m(m-1)/2`
strict upper-triangle pairs and `Aggregation.Em` has an outer factor two, so
`m² * eps` is a valid (slightly coarse) total error. -/
def blockDelta (eps : ℝ) : ℝ := (Current.m : ℝ) ^ 2 * eps

/-- The primitive compact-uniform Gram statement needed by the current
deduction.  It is guarded by the actual normalized separation, not by an
index-distance surrogate. -/
structure PairwiseGramData {d r : ℕ} (y : Fin r → ℝ)
    (V : Matrix (Fin d) (Fin r) ℂ) (eps : ℝ) : Prop where
  eps_nonneg : 0 ≤ eps
  close : ∀ i j : Fin r, (i : ℕ) < (j : ℕ) →
    y j - y i < CurrentBlock.D →
    CurrentWindow.weight (y j - y i) ≤ ‖(Vᴴ * V) i j‖ ^ 2 + eps

/-- Pairwise compact-uniform control implies the aggregate guarded Gram
inequality required by `CurrentBlockMatrix.paper_block_matrix`. -/
theorem PairwiseGramData.guardedBlockApprox
    {d r : ℕ} {y : Fin r → ℝ} {V : Matrix (Fin d) (Fin r) ℂ}
    {eps : ℝ} (h : PairwiseGramData y V eps) (hy : StrictMono y)
    {K t : ℕ} (hKt : t + K * Current.m ≤ r) (c : Fin K) :
    let e := blockEmb hKt c
    y (e ⟨Current.m - 1, by norm_num [Current.m]⟩) -
          y (e ⟨0, by norm_num [Current.m]⟩) < CurrentBlock.D →
      Aggregation.Em CurrentWindow.weight (fun i => y (e i)) ≤
        CurrentBlockMatrix.offDiagEnergy ((Vᴴ * V).submatrix e e) + blockDelta eps := by
  dsimp only
  let e := blockEmb hKt c
  let yB : Fin Current.m → ℝ := fun i => y (e i)
  intro hspan
  have hpair : ∀ j : Fin Current.m, ∀ i ∈ Finset.Iio j,
      CurrentWindow.weight (yB j - yB i) ≤
        ‖((Vᴴ * V).submatrix e e) i j‖ ^ 2 + eps := by
    intro j i hij
    rw [Finset.mem_Iio, Fin.lt_def] at hij
    have heij : (e i : ℕ) < (e j : ℕ) := by
      change t + (c : ℕ) * Current.m + (i : ℕ) <
        t + (c : ℕ) * Current.m + (j : ℕ)
      omega
    have hi0 : (e ⟨0, by norm_num [Current.m]⟩ : ℕ) ≤ (e i : ℕ) := by
      change t + (c : ℕ) * Current.m + 0 ≤
        t + (c : ℕ) * Current.m + (i : ℕ)
      omega
    have hjlast : (e j : ℕ) ≤
        (e ⟨Current.m - 1, by norm_num [Current.m]⟩ : ℕ) := by
      change t + (c : ℕ) * Current.m + (j : ℕ) ≤
        t + (c : ℕ) * Current.m + (Current.m - 1)
      have hj := j.isLt
      omega
    have hdist : y (e j) - y (e i) < CurrentBlock.D := by
      have hlo := hy.monotone hi0
      have hhi := hy.monotone hjlast
      linarith
    exact h.close (e i) (e j) heij hdist
  have hstep :
      ∑ j : Fin Current.m, ∑ i ∈ Finset.Iio j,
          CurrentWindow.weight (yB j - yB i) ≤
        ∑ j : Fin Current.m, ∑ i ∈ Finset.Iio j,
          (‖((Vᴴ * V).submatrix e e) i j‖ ^ 2 + eps) :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i hi => hpair j i hi
  have hcntEq : ∑ j : Fin Current.m, ∑ _i ∈ Finset.Iio j, eps =
      ((Current.m : ℝ) * ((Current.m : ℝ) - 1) / 2) * eps := by
    simp_rw [Finset.sum_const, nsmul_eq_mul, Fin.card_Iio]
    change (∑ x : Fin Current.m, (((x : ℕ) : ℝ) * eps)) = _
    calc
      ∑ x : Fin Current.m, (((x : ℕ) : ℝ) * eps) =
          ∑ x ∈ Finset.range Current.m, (x : ℝ) * eps :=
            Fin.sum_univ_eq_sum_range (fun x : ℕ => (x : ℝ) * eps) Current.m
      _ = _ := by
        rw [← Finset.sum_mul]
        norm_num [Finset.sum_range_id, Current.m]
  have hcnt : 2 * (∑ j : Fin Current.m, ∑ _i ∈ Finset.Iio j, eps) ≤
      (Current.m : ℝ) ^ 2 * eps := by
    rw [hcntEq]
    have hm : (0 : ℝ) ≤ Current.m := by positivity
    nlinarith [h.eps_nonneg]
  have hdist :
      ∑ j : Fin Current.m, ∑ i ∈ Finset.Iio j,
          (‖((Vᴴ * V).submatrix e e) i j‖ ^ 2 + eps) =
        (∑ j : Fin Current.m, ∑ i ∈ Finset.Iio j,
          ‖((Vᴴ * V).submatrix e e) i j‖ ^ 2) +
        ∑ j : Fin Current.m, ∑ _i ∈ Finset.Iio j, eps := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_add_distrib
  have hswap :
      ∑ j : Fin Current.m, ∑ i ∈ Finset.Iio j,
          ‖((Vᴴ * V).submatrix e e) i j‖ ^ 2 =
        ∑ i : Fin Current.m, ∑ j ∈ Finset.Ioi i,
          ‖((Vᴴ * V).submatrix e e) i j‖ ^ 2 :=
    Aggregation.sum_Iio_swap
      (fun j i => ‖((Vᴴ * V).submatrix e e) i j‖ ^ 2)
  have hsum :
      2 * (∑ j : Fin Current.m, ∑ i ∈ Finset.Iio j,
          CurrentWindow.weight (yB j - yB i)) ≤
        2 * (∑ i : Fin Current.m, ∑ j ∈ Finset.Ioi i,
          ‖((Vᴴ * V).submatrix e e) i j‖ ^ 2) +
        (Current.m : ℝ) ^ 2 * eps := by
    linarith [hstep, hcnt, hdist]
  unfold Aggregation.Em CurrentBlockMatrix.offDiagEnergy blockDelta
  exact hsum

/-! ## Primitive moment data imply the stability seam -/

/-- Exact error produced by the trace and Frobenius moment bounds. -/
def stabilityError (R₁ R₂ : ℝ) : ℝ := 4 * R₁ + R₂

/-- Primitive matrix/counting data from which the stability seam follows.
Unlike `CurrentAssembly.FiniteHeightInputs.stabilitySeam`, this structure does
not assume any inequality containing the target spectral defect. -/
structure MomentData {d r : ℕ} (b : ℕ) (N R₁ R₂ : ℝ)
    (V : Matrix (Fin d) (Fin r) ℂ) (Q : Matrix (Fin d) (Fin d) ℂ) : Prop where
  col_le : ∀ j, StabilityRankTrace.colSq V j ≤ 1
  Q_hermitian : Q.IsHermitian
  positive_index : RHLinalg.posIndex Q_hermitian ≤ b
  count_seam : 3 * (r : ℝ) + 4 * (b : ℝ) ≤ (r : ℝ) + 2 * N
  trace_lower : N - R₁ ≤ RHLinalg.rtrace (V * Vᴴ + Q)
  frobenius_upper : RHLinalg.frobSq (V * Vᴴ + Q) ≤
    (2 - Current.Hcert) * N + R₂

/-- The imported stability rank--trace theorem turns primitive moment data
into exactly the current defect seam. -/
theorem MomentData.stabilitySeam
    {d r b : ℕ} {N R₁ R₂ : ℝ}
    {V : Matrix (Fin d) (Fin r) ℂ} {Q : Matrix (Fin d) (Fin d) ℂ}
    (h : MomentData b N R₁ R₂ V Q) :
    Current.Hcert * N +
        CurrentAssembly.globalDefect (Vᴴ * V)
          (Matrix.posSemidef_conjTranspose_mul_self V) -
        stabilityError R₁ R₂ ≤ (r : ℝ) := by
  have hs := Stability.stability_seam_moment
    h.col_le h.Q_hermitian h.positive_index h.count_seam
    h.trace_lower h.frobenius_upper
  simp_rw [Bridge.Psi_eq] at hs
  unfold CurrentAssembly.globalDefect stabilityError
  linarith

/-! ## Combined interface and assembly -/

/-- A strictly more primitive one-height interface than
`CurrentAssembly.FiniteHeightInputs`: the Gram matrix is forced to be
`VᴴV`, the stability seam is replaced by moment/count data, and the guarded
aggregate Gram bound is replaced by pairwise compact-uniform squared-energy
control. Deriving that estimate from ordinary entrywise Gram convergence is
still an explicit analytic obligation. -/
structure FiniteAnalyticInputs
    (d r b : ℕ) (N spanError eps R₁ R₂ : ℝ) where
  finiteWindow : CurrentWindow.FiniteWindowInputs
  r_pos : 0 < r
  N_nonneg : 0 ≤ N
  spanError_nonneg : 0 ≤ spanError
  y : Fin r → ℝ
  y_strictMono : StrictMono y
  V : Matrix (Fin d) (Fin r) ℂ
  Q : Matrix (Fin d) (Fin d) ℂ
  gram : PairwiseGramData y V eps
  moments : MomentData b N R₁ R₂ V Q
  spanControl :
    y ⟨r - 1, by omega⟩ - y ⟨0, r_pos⟩ ≤ N + spanError
  delta_small : Current.eta * blockDelta eps ≤ Current.R

/-- The smaller primitive interface discharges the complete one-height
assembly record. -/
def FiniteAnalyticInputs.toFiniteHeightInputs
    {d r b : ℕ} {N spanError eps R₁ R₂ : ℝ}
    (h : FiniteAnalyticInputs d r b N spanError eps R₁ R₂) :
    CurrentAssembly.FiniteHeightInputs r N (stabilityError R₁ R₂)
      spanError (blockDelta eps) where
  finiteWindow := h.finiteWindow
  r_pos := h.r_pos
  N_nonneg := h.N_nonneg
  delta_nonneg := by
    exact mul_nonneg (sq_nonneg _) h.gram.eps_nonneg
  delta_small := h.delta_small
  spanError_nonneg := h.spanError_nonneg
  y := h.y
  y_strictMono := h.y_strictMono
  G := h.Vᴴ * h.V
  G_posSemidef := Matrix.posSemidef_conjTranspose_mul_self h.V
  block_strictMono := by
    intro K t hKt c i j hij
    apply h.y_strictMono
    rw [Fin.lt_def] at hij ⊢
    change t + (c : ℕ) * Current.m + (i : ℕ) <
      t + (c : ℕ) * Current.m + (j : ℕ)
    omega
  guardedGramApprox := by
    intro K t hKt c
    exact h.gram.guardedBlockApprox h.y_strictMono hKt c
  spanControl := h.spanControl
  stabilitySeam := h.moments.stabilitySeam

/-- Filter-level primitive interface.  Dimensions of the ambient atom space
and the positive-index allowance may vary with height and therefore remain
existential at each height. -/
structure AsymptoticAnalyticInputs {X : Type*} (l : Filter X) where
  r : X → ℕ
  N : X → ℝ
  spanError : X → ℝ
  eps : X → ℝ
  R₁ : X → ℝ
  R₂ : X → ℝ
  eventuallyAnalytic : ∀ᶠ x in l, ∃ d b : ℕ,
    Nonempty (FiniteAnalyticInputs d (r x) b (N x) (spanError x)
      (eps x) (R₁ x) (R₂ x))
  errorsAreSmall : ∀ eta > 0, ∀ᶠ x in l,
    stabilityError (R₁ x) (R₂ x) +
        CurrentAssembly.assembledBlockError (r x) (blockDelta (eps x))
          (spanError x) ≤
      (1 - Current.R / (Current.m : ℝ)) * eta * N x

/-- Conversion to the already-audited generic assembly. -/
def AsymptoticAnalyticInputs.toAssembly
    {X : Type*} {l : Filter X} (h : AsymptoticAnalyticInputs l) :
    CurrentAssembly.AsymptoticInputs l where
  r := h.r
  N := h.N
  stabilityError := fun x => stabilityError (h.R₁ x) (h.R₂ x)
  spanError := h.spanError
  delta := fun x => blockDelta (h.eps x)
  eventuallyHeight := by
    filter_upwards [h.eventuallyAnalytic] with x hx
    obtain ⟨d, b, hx⟩ := hx
    exact hx.map FiniteAnalyticInputs.toFiniteHeightInputs
  errorsAreSmall := h.errorsAreSmall

/-- The rational current target follows from the smaller primitive analytic
interface without any additional analytic assumption. -/
theorem AsymptoticAnalyticInputs.target
    {X : Type*} {l : Filter X} (h : AsymptoticAnalyticInputs l) :
    ∀ᶠ x in l, Current.target * h.N x ≤ (h.r x : ℝ) :=
  h.toAssembly.target

end Zeta23Ext.CurrentAnalyticBridge
