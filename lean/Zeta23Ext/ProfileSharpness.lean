/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.SqrtProfile
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Star.Real

/-!
# Sharpness of the square-root profile

This file gives the constant-correlation examples showing that the profile in
`SqrtProfile.block_defect_sqrt` is sharp.  In dimension `N >= 2`, put

* `t = sqrt (E (N - 1) / N)`,
* `rho = t / (N - 1)`,
* `a = 1 + t`, and `b = 1 - rho`.

The matrix is `b I + rho J`, where `J` is the all-ones rank-one matrix.  Thus the
constant vector has eigenvalue `a`, every zero-sum vector has eigenvalue `b`, its
diagonal is one, and its doubled strict-upper-triangle energy is exactly `E`.
Whenever `b >= 0` the matrix is positive semidefinite.  The corresponding spectral
defect is

`Psi(a) + (N - 1) Psi(b) = h(E (N - 1) / N) + E / N`,

and therefore tends to `h(E)` as `N -> infinity`.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open Matrix Finset Filter Topology
open scoped BigOperators

namespace Zeta23Ext.ProfileSharpness

open Zeta23Ext.SqrtProfile Zeta23Ext.StabilityRankTrace

/-- The amount by which the exceptional eigenvalue exceeds one. -/
def t (E : ℝ) (N : ℕ) : ℝ := Real.sqrt (E * ((N : ℝ) - 1) / N)

/-- The common off-diagonal correlation. -/
def rho (E : ℝ) (N : ℕ) : ℝ := t E N / ((N : ℝ) - 1)

/-- The exceptional (constant-vector) eigenvalue. -/
def a (E : ℝ) (N : ℕ) : ℝ := 1 + t E N

/-- The repeated (zero-sum-subspace) eigenvalue. -/
def b (E : ℝ) (N : ℕ) : ℝ := 1 - rho E N

/-- The real constant-correlation matrix. -/
def corrMatrix (E : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  b E N • (1 : Matrix (Fin N) (Fin N) ℝ) +
    rho E N • Matrix.vecMulVec (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))

lemma t_nonneg (E : ℝ) (N : ℕ) : 0 ≤ t E N := Real.sqrt_nonneg _

lemma rho_nonneg (E : ℝ) {N : ℕ} (hN : 2 ≤ N) : 0 ≤ rho E N := by
  unfold rho
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  exact div_nonneg (t_nonneg E N) (by linarith)

lemma t_sq {E : ℝ} (hE : 0 ≤ E) {N : ℕ} (hN : 2 ≤ N) :
    t E N ^ 2 = E * ((N : ℝ) - 1) / N := by
  rw [t, Real.sq_sqrt]
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  exact div_nonneg (mul_nonneg hE (by linarith)) (by positivity)

lemma rho_mul_N_sub_one (E : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    rho E N * ((N : ℝ) - 1) = t E N := by
  unfold rho
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  exact div_mul_cancel₀ _ (by linarith)

@[simp] lemma corrMatrix_apply_same (E : ℝ) {N : ℕ} (i : Fin N) :
    corrMatrix E N i i = 1 := by
  simp [corrMatrix, b, Matrix.vecMulVec_apply]

@[simp] lemma corrMatrix_apply_ne (E : ℝ) {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    corrMatrix E N i j = rho E N := by
  simp [corrMatrix, Matrix.vecMulVec_apply, hij]

/-- The constant vector is an eigenvector with eigenvalue `a`. -/
lemma mulVec_one (E : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    corrMatrix E N *ᵥ (fun _ : Fin N => (1 : ℝ)) =
      a E N • (fun _ : Fin N => (1 : ℝ)) := by
  rw [corrMatrix, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec]
  ext i
  simp [Matrix.vecMulVec_mulVec, dotProduct, a, b]
  nlinarith [rho_mul_N_sub_one E hN]

/-- Every zero-sum vector is an eigenvector with eigenvalue `b`. -/
lemma mulVec_eq_b_smul_of_sum_eq_zero (E : ℝ) {N : ℕ} (x : Fin N → ℝ)
    (hx : ∑ i, x i = 0) :
    corrMatrix E N *ᵥ x = b E N • x := by
  rw [corrMatrix, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec]
  simp [Matrix.vecMulVec_mulVec, dotProduct, hx]

/-- Action of the rank-one perturbation on an arbitrary vector. -/
lemma mulVec_formula (E : ℝ) {N : ℕ} (x : Fin N → ℝ) :
    corrMatrix E N *ᵥ x =
      b E N • x + (rho E N * ∑ i, x i) • (fun _ : Fin N => (1 : ℝ)) := by
  rw [corrMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  ext i
  simp [Matrix.vecMulVec_mulVec, dotProduct]

/-- The constant-correlation matrix is positive semidefinite as soon as its repeated
eigenvalue `b` is nonnegative. -/
lemma corrMatrix_posSemidef {E : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hb : 0 ≤ b E N) : (corrMatrix E N).PosSemidef := by
  unfold corrMatrix
  exact (Matrix.PosSemidef.one.smul hb).add
    ((Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin N => (1 : ℝ))).smul
      (rho_nonneg E hN))

lemma corrMatrix_isHermitian (E : ℝ) (N : ℕ) : (corrMatrix E N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [corrMatrix, Matrix.vecMulVec_apply]
  · simp [corrMatrix, Matrix.vecMulVec_apply, hij, Ne.symm hij]

/-- Every actual Hermitian eigenvalue of the construction is either the exceptional
value `a` or the repeated value `b`. -/
lemma eigenvalue_eq_a_or_b (E : ℝ) {N : ℕ} (hN : 2 ≤ N) (k : Fin N) :
    let hG := corrMatrix_isHermitian E N
    hG.eigenvalues k = a E N ∨ hG.eigenvalues k = b E N := by
  let hG := corrMatrix_isHermitian E N
  let v : Fin N → ℝ := ⇑(hG.eigenvectorBasis k)
  have hv : v ≠ 0 := by
    exact (WithLp.ofLp_eq_zero 2).ne.2 (hG.eigenvectorBasis.orthonormal.ne_zero k)
  have heig : corrMatrix E N *ᵥ v = hG.eigenvalues k • v :=
    hG.mulVec_eigenvectorBasis k
  by_cases hs : ∑ i, v i = 0
  · right
    rw [mulVec_eq_b_smul_of_sum_eq_zero E v hs] at heig
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have hi' := congrFun heig i
    simp only [Pi.smul_apply, smul_eq_mul] at hi'
    have hz : (b E N - hG.eigenvalues k) * v i = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith
    · exact (hi hz).elim
  · left
    rw [mulVec_formula] at heig
    have hpoint : ∀ i : Fin N,
        (1 - rho E N) * v i + rho E N * (∑ j, v j) =
          hG.eigenvalues k * v i := by
      intro i
      have hi := congrFun heig i
      simpa [b] using hi
    have hsum : (∑ i : Fin N,
        ((1 - rho E N) * v i + rho E N * (∑ j, v j))) =
          ∑ i : Fin N, hG.eigenvalues k * v i :=
      Finset.sum_congr rfl fun i _ => hpoint i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have hr := rho_mul_N_sub_one E hN
    change hG.eigenvalues k = 1 + t E N
    have hcoef : 1 - rho E N + (N : ℝ) * rho E N = 1 + t E N := by
      nlinarith
    have hz : (hG.eigenvalues k - (1 + t E N)) * (∑ i, v i) = 0 := by
      calc
        (hG.eigenvalues k - (1 + t E N)) * (∑ i, v i) =
            hG.eigenvalues k * (∑ i, v i) -
              (1 - rho E N + (N : ℝ) * rho E N) * (∑ i, v i) := by
                rw [hcoef]
                ring
        _ = 0 := by nlinarith [hsum]
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith
    · exact (hs hz).elim

/-- The number of strict-upper-triangle positions in an `N x N` matrix, in a form
that avoids division by two. -/
lemma two_mul_sum_card_Ioi (N : ℕ) :
    2 * (∑ i : Fin N, #(Finset.Ioi i)) = N * (N - 1) := by
  simp_rw [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range, Finset.sum_range_reflect (fun i => i) N]
  simpa [Nat.mul_comm] using Finset.sum_range_id_mul_two N

/-- Exact off-diagonal energy of the construction. -/
theorem corrMatrix_energy {E : ℝ} (hE : 0 ≤ E) {N : ℕ} (hN : 2 ≤ N) :
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖corrMatrix E N i j‖ ^ 2 = E := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hN0 : (0 : ℝ) < N := by positivity
  have hcard := two_mul_sum_card_Ioi N
  have hinner : ∀ i : Fin N,
      ∑ j ∈ Finset.Ioi i, ‖corrMatrix E N i j‖ ^ 2 =
        (#(Finset.Ioi i) : ℝ) * rho E N ^ 2 := by
    intro i
    calc
      ∑ j ∈ Finset.Ioi i, ‖corrMatrix E N i j‖ ^ 2
          = ∑ _j ∈ Finset.Ioi i, rho E N ^ 2 := by
              refine Finset.sum_congr rfl fun j hj => ?_
              rw [corrMatrix_apply_ne E i j (ne_of_lt (Finset.mem_Ioi.mp hj)),
                Real.norm_eq_abs, sq_abs]
      _ = (#(Finset.Ioi i) : ℝ) * rho E N ^ 2 := by simp
  simp_rw [hinner]
  rw [← Finset.sum_mul]
  have hcardR : 2 * (∑ i : Fin N, (#(Finset.Ioi i) : ℝ)) =
      (N : ℝ) * ((N : ℝ) - 1) := by
    calc
      2 * (∑ i : Fin N, (#(Finset.Ioi i) : ℝ)) =
          ((2 * ∑ i : Fin N, #(Finset.Ioi i) : ℕ) : ℝ) := by push_cast; ring
      _ = ((N * (N - 1) : ℕ) : ℝ) := by rw [hcard]
      _ = (N : ℝ) * ((N : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  rw [rho, div_pow, t_sq hE hN]
  field_simp
  nlinarith [hcardR]

/-- The formal eigenvalue multiset of the rank-one construction: one copy of `a` and
`N-1` copies of `b`. -/
def spectralDefect (E : ℝ) (N : ℕ) : ℝ :=
  Psi (a E N) + ((N : ℝ) - 1) * Psi (b E N)

lemma corrMatrix_trace (E : ℝ) (N : ℕ) :
    (corrMatrix E N).trace = (N : ℝ) := by
  unfold Matrix.trace
  calc
    (∑ i : Fin N, corrMatrix E N i i) = ∑ _i : Fin N, (1 : ℝ) :=
      Finset.sum_congr rfl fun i _ => corrMatrix_apply_same E i
    _ = (N : ℝ) := by simp

/-- The named spectral defect is the actual `Psi`-sum of Mathlib's Hermitian
eigenvalue array.  The proof does not assume an ordering or multiplicity convention:
every eigenvalue is first shown to be `a` or `b`, and the trace fixes the aggregate
multiplicity. -/
theorem sum_Psi_eigenvalues_eq_spectralDefect (E : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    (∑ k, Psi ((corrMatrix_isHermitian E N).eigenvalues k)) = spectralDefect E N := by
  let hG := corrMatrix_isHermitian E N
  have heigs : ∀ k : Fin N, hG.eigenvalues k = a E N ∨ hG.eigenvalues k = b E N :=
    fun k => eigenvalue_eq_a_or_b E hN k
  have hsumEig : (∑ k, hG.eigenvalues k) = (N : ℝ) := by
    have ht := hG.trace_eq_sum_eigenvalues
    rw [corrMatrix_trace E N] at ht
    simpa using ht.symm
  have hr := rho_mul_N_sub_one E hN
  have habalance : a E N + ((N : ℝ) - 1) * b E N = (N : ℝ) := by
    unfold a b
    nlinarith
  by_cases hab : a E N = b E N
  · have heq : ∀ k : Fin N, hG.eigenvalues k = b E N := by
      intro k
      rcases heigs k with hk | hk
      · exact hk.trans hab
      · exact hk
    simp_rw [heq]
    rw [spectralDefect, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hab]
    ring
  · have hpoint : ∀ k : Fin N,
        (a E N - b E N) * Psi (hG.eigenvalues k) =
          (hG.eigenvalues k - b E N) * Psi (a E N) +
            (a E N - hG.eigenvalues k) * Psi (b E N) := by
      intro k
      rcases heigs k with hk | hk <;> rw [hk] <;> ring
    have hscaled : (a E N - b E N) * (∑ k, Psi (hG.eigenvalues k)) =
        (a E N - b E N) * spectralDefect E N := by
      rw [Finset.mul_sum]
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      simp_rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [hsumEig]
      unfold spectralDefect
      linear_combination (Psi (b E N) - Psi (a E N)) * habalance
    exact mul_left_cancel₀ (sub_ne_zero.mpr hab) hscaled

/-- Exact finite-dimensional defect formula. -/
theorem spectralDefect_eq {E : ℝ} (hE : 0 ≤ E) {N : ℕ} (hN : 2 ≤ N)
    (hb : 0 ≤ b E N) :
    spectralDefect E N = sqrtProfile (E * ((N : ℝ) - 1) / N) + E / N := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have ha0 : 0 ≤ a E N := by unfold a; linarith [t_nonneg E N]
  have hr0 := rho_nonneg E hN
  have hr1 : rho E N ≤ 1 := by unfold b at hb; linarith
  rw [spectralDefect, Psi_eq_sqrtProfile_sq_sub_one ha0,
    Psi_eq_sqrtProfile_sq_sub_one hb]
  have ha : (a E N - 1) ^ 2 = E * ((N : ℝ) - 1) / N := by
    unfold a
    simpa using t_sq hE hN
  have hb' : (b E N - 1) ^ 2 = rho E N ^ 2 := by unfold b; ring
  rw [ha, hb']
  have hrSq : rho E N ^ 2 ≤ 1 := by nlinarith [sq_nonneg (rho E N)]
  rw [sqrtProfile_of_le_one hrSq]
  rw [rho, div_pow, t_sq hE hN]
  field_simp

/-- A denominator-safe sequence of the exact finite defects, using dimension `n+2`. -/
def defectSequence (E : ℝ) (n : ℕ) : ℝ :=
  sqrtProfile (E * ((((n : ℝ) + 2) - 1) / ((n : ℝ) + 2))) + E / ((n : ℝ) + 2)

lemma continuous_sqrtProfile : Continuous sqrtProfile := by
  unfold sqrtProfile
  apply continuous_if_le
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · intro x hx
    subst x
    norm_num

/-- The exact defects of the constant-correlation construction converge to the sharp
profile. -/
theorem tendsto_defectSequence (E : ℝ) :
    Tendsto (defectSequence E) atTop (nhds (sqrtProfile E)) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (nhds 0) := by
    apply (tendsto_inv_atTop_zero.comp hden).congr'
    filter_upwards with n
    simp only [Function.comp_apply, one_div]
  have hratio : Tendsto (fun n : ℕ => (((n : ℝ) + 2) - 1) / ((n : ℝ) + 2))
      atTop (nhds 1) := by
    have heq : (fun n : ℕ => (((n : ℝ) + 2) - 1) / ((n : ℝ) + 2)) =
        fun n : ℕ => 1 - 1 / ((n : ℝ) + 2) := by
      funext n
      field_simp
    rw [heq]
    simpa using tendsto_const_nhds.sub hinv
  have harg : Tendsto (fun n : ℕ => E * ((((n : ℝ) + 2) - 1) / ((n : ℝ) + 2)))
      atTop (nhds E) := by
    simpa using tendsto_const_nhds.mul hratio
  have htail : Tendsto (fun n : ℕ => E / ((n : ℝ) + 2)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  change Tendsto (fun n : ℕ =>
    sqrtProfile (E * ((((n : ℝ) + 2) - 1) / ((n : ℝ) + 2))) +
      E / ((n : ℝ) + 2)) atTop (nhds (sqrtProfile E))
  simpa only [Function.comp_apply, add_zero] using
    ((continuous_sqrtProfile.tendsto E).comp harg).add htail

/-- Along the dimensions `N=n+2`, the eigenvalue-sum formula converges to `h(E)`.
This statement is independent of the eventually-true PSD side condition `b >= 0`;
that condition is used only to realize the formula by positive semidefinite matrices. -/
theorem tendsto_spectralDefect_formula (E : ℝ) :
    Tendsto (defectSequence E) atTop (nhds (sqrtProfile E)) :=
  tendsto_defectSequence E

/-- The repeated eigenvalue is nonnegative in all sufficiently large dimensions. -/
theorem eventually_b_nonneg {E : ℝ} (hE : 0 ≤ E) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ b E (n + 2) := by
  obtain ⟨K, hK⟩ := exists_nat_ge (Real.sqrt E)
  filter_upwards [eventually_ge_atTop K] with n hn
  have hnR : (K : ℝ) ≤ n := by exact_mod_cast hn
  have hsN : Real.sqrt E ≤ (n : ℝ) + 1 := by linarith
  have hden : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hratio : (((n + 2 : ℕ) : ℝ) - 1) / ((n + 2 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hden]
    norm_num
  have harg : E * (((n + 2 : ℕ) : ℝ) - 1) / ((n + 2 : ℕ) : ℝ) ≤ E := by
    rw [mul_div_assoc]
    nlinarith [mul_le_mul_of_nonneg_left hratio hE]
  have ht : t E (n + 2) ≤ Real.sqrt E := by
    unfold t
    exact Real.sqrt_le_sqrt harg
  unfold b rho
  apply sub_nonneg.mpr
  have hden1 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) - 1 := by
    have : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 < n + 2 by omega)
    linarith
  rw [div_le_one hden1]
  have hsN' : Real.sqrt E ≤ ((n + 2 : ℕ) : ℝ) - 1 := by
    convert hsN using 1
    norm_num
    ring
  exact ht.trans hsN'

/-- Hence the constant-correlation matrices in the sharpness sequence are eventually
positive semidefinite. -/
theorem eventually_corrMatrix_posSemidef {E : ℝ} (hE : 0 ≤ E) :
    ∀ᶠ n : ℕ in atTop, (corrMatrix E (n + 2)).PosSemidef := by
  filter_upwards [eventually_b_nonneg hE] with n hb
  exact corrMatrix_posSemidef (by omega) hb

/-- The actual spectral `Psi`-trace of the dimension-`n+2` matrix. -/
def actualDefect (E : ℝ) (n : ℕ) : ℝ :=
  ∑ k, Psi ((corrMatrix_isHermitian E (n + 2)).eigenvalues k)

theorem eventually_actualDefect_eq_defectSequence {E : ℝ} (hE : 0 ≤ E) :
    ∀ᶠ n : ℕ in atTop, actualDefect E n = defectSequence E n := by
  filter_upwards [eventually_b_nonneg hE] with n hb
  calc
    actualDefect E n = spectralDefect E (n + 2) := by
      exact sum_Psi_eigenvalues_eq_spectralDefect E (by omega)
    _ = sqrtProfile (E * ((((n + 2 : ℕ) : ℝ) - 1)) / ((n + 2 : ℕ) : ℝ)) +
        E / ((n + 2 : ℕ) : ℝ) :=
      spectralDefect_eq hE (by omega) hb
    _ = defectSequence E n := by
      unfold defectSequence
      norm_num
      congr 2 <;> ring

/-- **Sharpness theorem.**  The actual `Psi`-traces of an eventually positive
semidefinite sequence of diagonal-one constant-correlation matrices, each with exact
off-diagonal energy `E`, converge to `sqrtProfile E`. -/
theorem tendsto_actualDefect {E : ℝ} (hE : 0 ≤ E) :
    Tendsto (actualDefect E) atTop (nhds (sqrtProfile E)) := by
  apply (tendsto_defectSequence E).congr'
  filter_upwards [eventually_actualDefect_eq_defectSequence hE] with n hn
  exact hn.symm

end Zeta23Ext.ProfileSharpness
