/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23Ext/StabilityRankTrace.lean — the stability-enhanced rank–trace inequality (Lemma 2.1
of the extension of Theorem D).

For `V` a d×r matrix over an RCLike field whose columns `v_j` satisfy `‖v_j‖² ≤ 1`, let
`P := V Vᴴ` (PSD), `M := Vᴴ V` (the Gram matrix), and let `Q` be Hermitian with `n₊(Q) ≤ b`.
With the stability profile `Ψ(t) = (t−1)²` for `0 ≤ t ≤ 2` and `2t−3` for `t ≥ 2`:

    ‖P + Q‖_F²  ≥  4·tr(P + Q) − 3r − 4b + tr Ψ(M),      tr Ψ(M) = Σ_i Ψ(μ_i(M)).

Proof: `Ψ = g₂ + 1` where `g_c(x) = x² − cx − ((x−c)₊)²` is the convex profile of
`Zeta23.ZeroSide.RankTraceMult`.  We replay the skeleton of `rank_trace_mult` (Q = Q₊ − Q₋,
drop tr(PQ₊) ≥ 0, von Neumann, the termwise scalar step, ‖Q₊‖² ≥ 2c·trQ₊ − c²b) but keep the
g_c-sum on the FULL spectrum of `P` (the Schur diagonal step is not needed), then transfer it
to the Gram spectrum via `sum_eigenvalues_comm` (spectra of `VVᴴ` and `VᴴV` agree away from 0
and `g_c(0) = 0`).  This gives the spectral inequality `rank_trace_gram`:

    c·tr P + Σ_j g_c(μ_j(M)) + 2c·tr Q − c²·b  ≤  ‖P + Q‖_F².

Specializing to `c = 2`, adding `r` to convert `g₂` to `Ψ`, and using `tr P = Σ_j ‖v_j‖² ≤ r`
(unit-bounded columns) yields the stated Lemma 2.1 (`stability_rank_trace`).  The Gram-side
defect bound `Σ_j Ψ(‖v_j‖²) ≤ Σ_j Ψ(μ_j(M))` (`sum_Psi_colSq_le`) is Schur–Jensen for `g₂`.
-/
import Zeta23.ZeroSide.RankTraceMult

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.StabilityRankTrace

open RHLinalg Zeta23.ZeroSide.RankTraceMult

/-! ### (A) the stability profile Ψ -/

/-- The stability profile `Ψ(t) = (t−1)²` for `t ≤ 2`, `= 2t − 3` for `t ≥ 2`.
Identically `Ψ = g₂ + 1` for the convex profile `g_c` of `RankTraceMult`. -/
def Psi (t : ℝ) : ℝ := gc 2 t + 1

lemma Psi_of_le {t : ℝ} (h : t ≤ 2) : Psi t = (t - 1) ^ 2 := by
  unfold Psi; rw [gc_of_le h]; ring

lemma Psi_of_ge {t : ℝ} (h : 2 ≤ t) : Psi t = 2 * t - 3 := by
  unfold Psi; rw [gc_of_ge h]; ring

@[simp] lemma Psi_zero : Psi 0 = 1 := by rw [Psi_of_le (by norm_num)]; norm_num

@[simp] lemma Psi_one : Psi 1 = 0 := by rw [Psi_of_le (by norm_num)]; norm_num

lemma Psi_nonneg (t : ℝ) : 0 ≤ Psi t := by
  have h := gc_ge (c := 2) (x := t) (by norm_num)
  unfold Psi; linarith

section Main

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### (B) columns and the Gram diagonal -/

/-- Squared norm of the `j`-th column of `V`:  `colSq V j = ‖v_j‖²`. -/
def colSq (V : Matrix n ι 𝕜) (j : ι) : ℝ := ∑ a, ‖V a j‖ ^ 2

lemma colSq_nonneg (V : Matrix n ι 𝕜) (j : ι) : 0 ≤ colSq V j :=
  Finset.sum_nonneg fun _a _ => sq_nonneg _

/-- The Gram matrix `M = Vᴴ V` has diagonal `re M_jj = ‖v_j‖²`. -/
lemma re_gram_diag (V : Matrix n ι 𝕜) (j : ι) :
    RCLike.re ((Vᴴ * V) j j) = colSq V j := by
  unfold colSq
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul,
    show (((‖V a j‖ : 𝕜) ^ 2 : 𝕜)) = ((‖V a j‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]

/-- `tr(V Vᴴ) = Σ_j ‖v_j‖²`. -/
lemma rtrace_self_mul_conjTranspose (V : Matrix n ι 𝕜) :
    rtrace (V * Vᴴ) = ∑ j, colSq V j := by
  unfold rtrace
  rw [trace_mul_comm]
  unfold Matrix.trace
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => re_gram_diag V j

/-! ### (C) the spectral (Gram-side) rank–trace inequality -/

/-- **Spectral rank–trace inequality**: for `P = V Vᴴ`, `M = Vᴴ V`, `Q` Hermitian with
`n₊(Q) ≤ b` and `c > 0`:

    c·tr P + Σ_j g_c(μ_j(M)) + 2c·tr Q − c²·b ≤ ‖P + Q‖_F²,

with the `g_c`-sum over the GRAM spectrum (strictly sharper than the diagonal form of
`rank_trace_mult`, by Schur–Jensen).  Any Hermiticity proof `hM` for `Vᴴ V` may be supplied. -/
theorem rank_trace_gram (V : Matrix n ι 𝕜) (hM : (Vᴴ * V).IsHermitian)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace (V * Vᴴ) + (∑ j, gc c (hM.eigenvalues j)) + 2 * c * rtrace Q - c ^ 2 * b
      ≤ frobSq (V * Vᴴ + Q) := by
  classical
  set P := V * Vᴴ with hPdef
  have hP : P.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  -- Positive/negative parts of Q (verbatim from rank_trace_mult).
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  set d := Fintype.card n
  set p : Fin d → ℝ := hP.isHermitian.eigenvalues₀
  set mm : Fin d → ℝ := hQm_psd.isHermitian.eigenvalues₀
  have hp_nn : ∀ k, 0 ≤ p k := fun k => by
    rw [show p k = hP.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hP.isHermitian k).symm]
    exact hP.eigenvalues_nonneg _
  have hm_nn : ∀ k, 0 ≤ mm k := fun k => by
    rw [show mm k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _
  have htraceP : rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian id
  have htraceQm : rtrace Qm = ∑ k, mm k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobP : frobSq P = ∑ k, (p k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian (· ^ 2)
  have hfrobQm : frobSq Qm = ∑ k, (mm k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  -- Step 1: Frobenius expansion.
  have hexpand : frobSq (P + Q)
      = frobSq P + 2 * RCLike.re (P * Qp).trace - 2 * RCLike.re (P * Qm).trace
        + frobSq Qp + frobSq Qm := by
    have h1 : frobSq (-Qm) = frobSq Qm := by unfold frobSq; rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by rw [mul_neg, hQpQm]; simp
    rw [hQdec, frobSq_add_hermitian hP.isHermitian (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm, frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  -- Step 2: drop tr(PQ₊) ≥ 0.
  have hPQp : 0 ≤ RCLike.re (P * Qp).trace := trace_mul_nonneg_of_posSemidef hP hQp_psd
  -- Step 3: von Neumann.
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * mm k :=
    vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  have hstep4 : ∑ k, (p k - mm k) ^ 2 ≤ frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - mm k) ^ 2
        = ∑ k, (p k)^2 - 2 * ∑ k, p k * mm k + ∑ k, (mm k)^2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]; linarith
  -- Step 5: spectrum transfer (VᴴV ↔ VVᴴ, g_c(0) = 0) in place of the Schur diagonal step.
  have hgc_eig : ∑ j, gc c (hM.eigenvalues j) = ∑ k, gc c (p k) := by
    calc ∑ j, gc c (hM.eigenvalues j)
        = ∑ i, gc c (hP.1.eigenvalues i) :=
          (sum_eigenvalues_comm V (gc c) (gc_zero hc.le)).symm
      _ = ∑ k, gc c (p k) := sum_eigenvalues_reindex hP.isHermitian (gc c)
  have hstep5 : c * rtrace P + (∑ j, gc c (hM.eigenvalues j)) - 2 * c * rtrace Qm
      ≤ ∑ k, (p k - mm k) ^ 2 := by
    rw [htraceP, htraceQm, hgc_eig]
    have := sum_sq_sub_ge_gc hp_nn hm_nn hc.le
    linarith
  -- Step 6: estimate on Q₊ (verbatim).
  have hstep6 : 2 * c * rtrace Qp - c^2 * b ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ c
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0} = #{i | 0 < hQ.eigenvalues i} := by
          congr 1; ext i; simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  have htraceQ : 2 * c * rtrace Q = 2 * c * rtrace Qp - 2 * c * rtrace Qm := by
    rw [hQdec, rtrace_sub]; ring
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ]

/-! ### (D) Lemma 2.1: the stability-enhanced rank–trace inequality -/

/-- **Stability-enhanced rank–trace inequality (Lemma 2.1).**  For `P = V Vᴴ` with
unit-bounded columns (`‖v_j‖² ≤ 1`), `M = Vᴴ V` the r×r Gram matrix, and `Q` Hermitian with
`n₊(Q) ≤ b`:

    4·tr(P + Q) − 3r − 4b + tr Ψ(M)  ≤  ‖P + Q‖_F²,

where `tr Ψ(M) = Σ_j Ψ(μ_j(M))` and `Ψ(t) = (t−1)²` on `[0,2]`, `= 2t − 3` beyond. -/
theorem stability_rank_trace (V : Matrix n ι 𝕜) (hV : ∀ j, colSq V j ≤ 1)
    (hM : (Vᴴ * V).IsHermitian)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card ι : ℝ) - 4 * b
        + ∑ j, Psi (hM.eigenvalues j)
      ≤ frobSq (V * Vᴴ + Q) := by
  have h := rank_trace_gram V hM hQ hb (c := 2) (by norm_num)
  have htrP : rtrace (V * Vᴴ) ≤ (Fintype.card ι : ℝ) := by
    rw [rtrace_self_mul_conjTranspose]
    calc ∑ j, colSq V j ≤ ∑ _j : ι, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card ι : ℝ) := by simp
  have hPsi : ∑ j, Psi (hM.eigenvalues j)
      = (∑ j, gc 2 (hM.eigenvalues j)) + (Fintype.card ι : ℝ) := by
    unfold Psi
    rw [Finset.sum_add_distrib]
    simp
  rw [rtrace_add, hPsi]
  linarith

/-- The `tr Ψ(M)` form via the repo's functional calculus:
`rtrace (specMap hM Psi) = Σ_j Ψ(μ_j(M))`. -/
lemma rtrace_specMap_Psi {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) :
    rtrace (specMap hM Psi) = ∑ j, Psi (hM.eigenvalues j) :=
  rtrace_specMap hM Psi

/-- Lemma 2.1 phrased with `tr Ψ(M)` as `rtrace (specMap hM Psi)`. -/
theorem stability_rank_trace_specMap (V : Matrix n ι 𝕜) (hV : ∀ j, colSq V j ≤ 1)
    (hM : (Vᴴ * V).IsHermitian)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card ι : ℝ) - 4 * b
        + rtrace (specMap hM Psi)
      ≤ frobSq (V * Vᴴ + Q) := by
  rw [rtrace_specMap_Psi hM]
  exact stability_rank_trace V hV hM hQ hb

/-! ### (E) Gram-side defect bounds and the column form -/

/-- **Gram-side defect lower bound** (Schur–Jensen for `Ψ`):
`Σ_j Ψ(‖v_j‖²) ≤ Σ_j Ψ(μ_j(M))` — the spectral stability term dominates the columnwise one. -/
theorem sum_Psi_colSq_le (V : Matrix n ι 𝕜) (hM : (Vᴴ * V).IsHermitian) :
    ∑ j, Psi (colSq V j) ≤ ∑ j, Psi (hM.eigenvalues j) := by
  unfold Psi
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hMps : (Vᴴ * V).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self V
  have h := sum_gc_diag_le_sum_gc_eigenvalues hMps (c := 2) (by norm_num)
  simp_rw [re_gram_diag V] at h
  exact add_le_add h le_rfl

/-- Lemma 2.1 with the (weaker) columnwise stability term `Σ_j Ψ(‖v_j‖²)`. -/
theorem stability_rank_trace_colSq (V : Matrix n ι 𝕜) (hV : ∀ j, colSq V j ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card ι : ℝ) - 4 * b + ∑ j, Psi (colSq V j)
      ≤ frobSq (V * Vᴴ + Q) := by
  have hM : (Vᴴ * V).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self V).1
  have h1 := stability_rank_trace V hV hM hQ hb
  have h2 := sum_Psi_colSq_le V hM
  linarith

end Main

/-! ### (F) the concrete ℂ, d×r specialization -/

/-- Lemma 2.1 over ℂ with concrete dimensions: `V : Matrix (Fin d) (Fin r) ℂ`. -/
theorem stability_rank_trace_complex {d r : ℕ} (V : Matrix (Fin d) (Fin r) ℂ)
    (hV : ∀ j, colSq V j ≤ 1) (hM : (Vᴴ * V).IsHermitian)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (r : ℝ) - 4 * b + ∑ j, Psi (hM.eigenvalues j)
      ≤ frobSq (V * Vᴴ + Q) := by
  simpa using stability_rank_trace V hV hM hQ hb

end Zeta23Ext.StabilityRankTrace
