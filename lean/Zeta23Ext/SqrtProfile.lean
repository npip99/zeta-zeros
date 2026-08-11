/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Aggregation
import Zeta23Ext.StabilityRankTrace
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The sharp square-root block profile

This file formalizes the scalar and matrix inequalities behind Lemma 3.1 of the
weighted-window extension.  The profile is

`h(E) = E` for `E ≤ 1`, and `h(E) = 2 * sqrt E - 1` for `1 ≤ E`.

The main matrix theorem is `block_defect_sqrt`: for a positive semidefinite Hermitian
matrix `G`, its spectral `Psi`-defect dominates `h` of twice the strict-upper-triangle
energy.  No normalization of the diagonal is needed for the lower bound.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.SqrtProfile

open RHLinalg

/-- The sharp square-root defect profile. -/
def sqrtProfile (E : ℝ) : ℝ := if E ≤ 1 then E else 2 * Real.sqrt E - 1

@[simp] lemma sqrtProfile_of_le_one {E : ℝ} (hE : E ≤ 1) : sqrtProfile E = E := by
  simp [sqrtProfile, hE]

lemma sqrtProfile_of_one_le {E : ℝ} (hE : 1 ≤ E) :
    sqrtProfile E = 2 * Real.sqrt E - 1 := by
  rcases hE.eq_or_lt with rfl | hE
  · norm_num [sqrtProfile]
  · simp [sqrtProfile, not_le_of_gt hE]

@[simp] lemma sqrtProfile_zero : sqrtProfile 0 = 0 := by simp [sqrtProfile]

@[simp] lemma sqrtProfile_one : sqrtProfile 1 = 1 := by simp [sqrtProfile]

lemma sqrtProfile_nonneg {E : ℝ} (hE : 0 ≤ E) : 0 ≤ sqrtProfile E := by
  rcases le_total E 1 with h | h
  · rw [sqrtProfile_of_le_one h]
    exact hE
  · rw [sqrtProfile_of_one_le h]
    have hs : 1 ≤ Real.sqrt E := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt h
    linarith

/-- The square-root branch never exceeds the identity on the nonnegative axis. -/
lemma sqrtProfile_le_self {E : ℝ} (hE : 0 ≤ E) : sqrtProfile E ≤ E := by
  rcases le_total E 1 with h | h
  · rw [sqrtProfile_of_le_one h]
  · rw [sqrtProfile_of_one_le h]
    nlinarith [Real.sq_sqrt hE, sq_nonneg (Real.sqrt E - 1)]

/-- The profile is monotone on the nonnegative axis. -/
lemma sqrtProfile_monoOn : MonotoneOn sqrtProfile (Set.Ici 0) := by
  intro x hx y hy hxy
  rcases le_total y 1 with hy1 | hy1
  · rw [sqrtProfile_of_le_one hy1, sqrtProfile_of_le_one (hxy.trans hy1)]
    exact hxy
  rcases le_total x 1 with hx1 | hx1
  · rw [sqrtProfile_of_le_one hx1, sqrtProfile_of_one_le hy1]
    have hs : 1 ≤ Real.sqrt y := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hy1
    linarith
  · rw [sqrtProfile_of_one_le hx1, sqrtProfile_of_one_le hy1]
    gcongr

/-- Subadditivity of the sharp profile on nonnegative arguments. -/
lemma sqrtProfile_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    sqrtProfile (x + y) ≤ sqrtProfile x + sqrtProfile y := by
  by_cases hxy : x + y ≤ 1
  · have hx1 : x ≤ 1 := le_trans (le_add_of_nonneg_right hy) hxy
    have hy1 : y ≤ 1 := le_trans (le_add_of_nonneg_left hx) hxy
    rw [sqrtProfile_of_le_one hxy, sqrtProfile_of_le_one hx1, sqrtProfile_of_le_one hy1]
  have hxy1 : 1 ≤ x + y := le_of_not_ge hxy
  rw [sqrtProfile_of_one_le hxy1]
  rcases le_total x 1 with hx1 | hx1 <;> rcases le_total y 1 with hy1 | hy1
  · rw [sqrtProfile_of_le_one hx1, sqrtProfile_of_le_one hy1]
    nlinarith [Real.sq_sqrt (add_nonneg hx hy), sq_nonneg (Real.sqrt (x + y) - 1)]
  · rw [sqrtProfile_of_le_one hx1, sqrtProfile_of_one_le hy1]
    have hsY : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy1
    have hsXY : Real.sqrt y ≤ Real.sqrt (x + y) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_left hx)
    have hsqY := Real.sq_sqrt hy
    have hsqXY := Real.sq_sqrt (add_nonneg hx hy)
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.sqrt (x + y) - Real.sqrt y)
      (by linarith : 0 ≤ Real.sqrt (x + y) + Real.sqrt y - 2)]
  · rw [sqrtProfile_of_one_le hx1, sqrtProfile_of_le_one hy1]
    have hsX : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
    have hsXY : Real.sqrt x ≤ Real.sqrt (x + y) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right hy)
    have hsqX := Real.sq_sqrt hx
    have hsqXY := Real.sq_sqrt (add_nonneg hx hy)
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.sqrt (x + y) - Real.sqrt x)
      (by linarith : 0 ≤ Real.sqrt (x + y) + Real.sqrt x - 2)]
  · rw [sqrtProfile_of_one_le hx1, sqrtProfile_of_one_le hy1]
    have hsX : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
    have hsY : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy1
    have hsR : 0 ≤ Real.sqrt x + Real.sqrt y - 1 / 2 := by linarith
    have hsqX := Real.sq_sqrt hx
    have hsqY := Real.sq_sqrt hy
    have hsqXY := Real.sq_sqrt (add_nonneg hx hy)
    have hprod : 0 ≤ (Real.sqrt x - 1) * (Real.sqrt y - 1) := mul_nonneg (by linarith) (by linarith)
    have hsquare : x + y ≤ (Real.sqrt x + Real.sqrt y - 1 / 2) ^ 2 := by nlinarith
    have hsqrt : Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y - 1 / 2 := by
      rw [Real.sqrt_le_left hsR]
      exact hsquare
    linarith

/-- A finite sum version of subadditivity. -/
lemma sqrtProfile_sum_le {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    sqrtProfile (∑ i, f i) ≤ ∑ i, sqrtProfile (f i) := by
  classical
  exact Finset.le_sum_of_subadditive_on_pred sqrtProfile (fun x : ℝ => 0 ≤ x)
    (by simp) (fun x y hx hy => sqrtProfile_add_le hx hy)
    (fun x y hx hy => add_nonneg hx hy) f (s := Finset.univ) (fun i _ => hf i)

/-- Mixed-branch Jensen inequality: the first point is below the junction and the
second is above it. -/
private lemma combo_low_high {x y a b : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy1 : 1 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * sqrtProfile x + b * sqrtProfile y ≤ sqrtProfile (a * x + b * y) := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy1
  rw [sqrtProfile_of_le_one hx1, sqrtProfile_of_one_le hy1]
  let z := a * x + b * y
  have hz0 : 0 ≤ z := add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0)
  rcases le_total z 1 with hz1 | hz1
  · rw [sqrtProfile_of_le_one hz1]
    dsimp [z]
    have hprofY := sqrtProfile_le_self hy0
    rw [sqrtProfile_of_one_le hy1] at hprofY
    nlinarith
  · rw [sqrtProfile_of_one_le hz1]
    have ht : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy1
    have hsqY := Real.sq_sqrt hy0
    have hden : 1 - x ≤ b * (y - x) := by
      dsimp [z] at hz1
      nlinarith
    have hfactor : 0 ≤ (Real.sqrt y - 1) *
        ((Real.sqrt y - 1) * (x + 3) + 2 * (1 - x)) := by positivity
    have hsep : (1 - x) * (y - x) ≤ (2 * Real.sqrt y - x - 1) ^ 2 := by
      nlinarith
    have hscale1 : (1 - x) ^ 2 ≤ b * ((1 - x) * (y - x)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx1)
        (sub_nonneg.mpr hden)]
    have hscale2 : b * ((1 - x) * (y - x)) ≤
        b * (2 * Real.sqrt y - x - 1) ^ 2 := mul_le_mul_of_nonneg_left hsep hb
    have hkey : (1 - x) ^ 2 ≤ b * (2 * Real.sqrt y - x - 1) ^ 2 :=
      hscale1.trans hscale2
    let q := (a * x + b * (2 * Real.sqrt y - 1) + 1) / 2
    have hq0 : 0 ≤ q := by
      dsimp [q]
      have hhy : 0 ≤ 2 * Real.sqrt y - 1 := by linarith
      positivity
    have hid : 4 * (z - q ^ 2) = a *
        (b * (2 * Real.sqrt y - x - 1) ^ 2 - (1 - x) ^ 2) := by
      dsimp [q, z]
      have haeq : a = 1 - b := by linarith
      rw [haeq]
      ring_nf
      nlinarith
    have hqSq : q ^ 2 ≤ z := by
      have hk : 0 ≤ b * (2 * Real.sqrt y - x - 1) ^ 2 - (1 - x) ^ 2 := by
        linarith
      nlinarith [mul_nonneg ha hk]
    have hqsqrt : q ≤ Real.sqrt z := (Real.le_sqrt hq0 hz0).2 hqSq
    dsimp [q, z] at hqsqrt ⊢
    linarith

/-- The sharp profile is concave on the nonnegative axis. -/
lemma sqrtProfile_concaveOn : ConcaveOn ℝ (Set.Ici 0) sqrtProfile := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rcases le_total x 1 with hx1 | hx1 <;> rcases le_total y 1 with hy1 | hy1
  · have hz1 : a * x + b * y ≤ 1 := by nlinarith
    rw [sqrtProfile_of_le_one hx1, sqrtProfile_of_le_one hy1,
      sqrtProfile_of_le_one hz1]
  · exact combo_low_high hx hx1 hy1 ha hb hab
  · simpa [add_comm, mul_comm] using combo_low_high hy hy1 hx1 hb ha (by linarith)
  · have hz1 : 1 ≤ a * x + b * y := by nlinarith
    rw [sqrtProfile_of_one_le hx1, sqrtProfile_of_one_le hy1,
      sqrtProfile_of_one_le hz1]
    have hs := Real.strictConcaveOn_sqrt.concaveOn.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hs
    linarith

/-- General chord inequality from the origin to any endpoint `A ≥ 1`. -/
lemma sqrtProfile_chord {A E : ℝ} (hA : 1 ≤ A) (hE0 : 0 ≤ E) (hEA : E ≤ A) :
    ((2 * Real.sqrt A - 1) / A) * E ≤ sqrtProfile E := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  rcases le_total E 1 with hE1 | hE1
  · rw [sqrtProfile_of_le_one hE1]
    have heta : (2 * Real.sqrt A - 1) / A ≤ 1 := by
      rw [div_le_one hApos]
      have hp := sqrtProfile_le_self (le_trans (by norm_num) hA)
      rw [sqrtProfile_of_one_le hA] at hp
      exact hp
    nlinarith
  · rw [sqrtProfile_of_one_le hE1, div_mul_eq_mul_div, div_le_iff₀ hApos]
    have hsE : 1 ≤ Real.sqrt E := Real.one_le_sqrt.mpr hE1
    have hsA : 1 ≤ Real.sqrt A := Real.one_le_sqrt.mpr hA
    have hsEA : Real.sqrt E ≤ Real.sqrt A := Real.sqrt_le_sqrt hEA
    have hsqE := Real.sq_sqrt hE0
    have hsqA := Real.sq_sqrt (le_trans (by norm_num) hA)
    have hfac : 0 ≤ (Real.sqrt A - Real.sqrt E) *
        (2 * Real.sqrt A * Real.sqrt E - Real.sqrt A - Real.sqrt E) := by
      apply mul_nonneg (by linarith)
      nlinarith [mul_nonneg (by linarith : 0 ≤ Real.sqrt A - 1)
        (by linarith : 0 ≤ Real.sqrt E - 1)]
    nlinarith

/-- The exact endpoint used by the weighted-window proof. -/
def blockA : ℝ := 31049 / 25000

/-- The exact chord slope `h(A)/A` used by the weighted-window proof. -/
def blockEta : ℝ := (2 * Real.sqrt blockA - 1) / blockA

lemma blockA_eq : blockA = (31049 : ℝ) / 25000 := rfl

lemma one_lt_blockA : (1 : ℝ) < blockA := by norm_num [blockA]

lemma block_chord {E : ℝ} (hE0 : 0 ≤ E) (hEA : E ≤ blockA) :
    blockEta * E ≤ sqrtProfile E := by
  exact sqrtProfile_chord one_lt_blockA.le hE0 hEA

lemma sqrtProfile_blockA : sqrtProfile blockA = 2 * Real.sqrt blockA - 1 := by
  exact sqrtProfile_of_one_le one_lt_blockA.le

/-- Exact scalar identity relating the stability profile to the square-root profile. -/
lemma Psi_eq_sqrtProfile_sq_sub_one {lam : ℝ} (hlam : 0 ≤ lam) :
    StabilityRankTrace.Psi lam = sqrtProfile ((lam - 1) ^ 2) := by
  by_cases hlam1 : lam ≤ 1
  · have hx : (lam - 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg lam]
    rw [StabilityRankTrace.Psi_of_le (hlam1.trans (by norm_num)), sqrtProfile_of_le_one hx]
  · have h1 : 1 ≤ lam := le_of_not_ge hlam1
    by_cases hlam2 : lam ≤ 2
    · have hx : (lam - 1) ^ 2 ≤ 1 := by nlinarith
      rw [StabilityRankTrace.Psi_of_le hlam2, sqrtProfile_of_le_one hx]
    · have h2 : 2 ≤ lam := le_of_not_ge hlam2
      have hx : 1 ≤ (lam - 1) ^ 2 := by nlinarith
      rw [StabilityRankTrace.Psi_of_ge h2, sqrtProfile_of_one_le hx,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith : 0 ≤ lam - 1)]
      ring

/-- The identical scalar identity for the copy of `Psi` used by `Aggregation`. -/
lemma aggregation_Psi_eq_sqrtProfile_sq_sub_one {lam : ℝ} (hlam : 0 ≤ lam) :
    Aggregation.Psi lam = sqrtProfile ((lam - 1) ^ 2) := by
  by_cases hlam1 : lam ≤ 1
  · have hx : (lam - 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg lam]
    rw [Aggregation.Psi_of_le (hlam1.trans (by norm_num)), sqrtProfile_of_le_one hx]
  · have h1 : 1 ≤ lam := le_of_not_ge hlam1
    by_cases hlam2 : lam ≤ 2
    · have hx : (lam - 1) ^ 2 ≤ 1 := by nlinarith
      rw [Aggregation.Psi_of_le hlam2, sqrtProfile_of_le_one hx]
    · have h2 : 2 ≤ lam := le_of_not_ge hlam2
      have hx : 1 ≤ (lam - 1) ^ 2 := by nlinarith
      rw [Aggregation.Psi_of_ge h2, sqrtProfile_of_one_le hx,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith : 0 ≤ lam - 1)]
      ring

/-! ## Matrix profile -/

/-- The Frobenius distance from the identity is the sum of the squared spectral
distances from `1` for a Hermitian matrix. -/
lemma frobSq_sub_one_eq_sum_sq_eigenvalues {m : ℕ} {G : Matrix (Fin m) (Fin m) 𝕜}
    [RCLike 𝕜] (hG : G.IsHermitian) :
    frobSq (G - 1) = ∑ i, (hG.eigenvalues i - 1) ^ 2 := by
  have h1 : frobSq (G - 1)
      = frobSq G - rtrace G - rtrace G + (Fintype.card (Fin m) : ℝ) := by
    have hexp : (G - 1)ᴴ * (G - 1) = Gᴴ * G - Gᴴ - G + 1 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
      noncomm_ring
    show RCLike.re ((G - 1)ᴴ * (G - 1)).trace = _
    rw [hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, map_add, map_sub,
      map_sub, Matrix.trace_conjTranspose, Matrix.trace_one]
    have hre : RCLike.re (star G.trace) = RCLike.re G.trace := by
      rw [RCLike.star_def, RCLike.conj_re]
    rw [hre]
    simp [frobSq, rtrace]
  rw [h1, frobSq_hermitian_eq_sum_sq_eigenvalues hG,
    rtrace_eq_sum_eigenvalues hG, Fintype.card_fin]
  have hexp2 : ∑ i, (hG.eigenvalues i - 1) ^ 2
      = ∑ i, (hG.eigenvalues i ^ 2 - hG.eigenvalues i - hG.eigenvalues i + 1) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hexp2, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Twice the strict-upper-triangle energy is bounded by the Frobenius distance
from the identity. -/
lemma offDiagEnergy_le_frobSq_sub_one {m : ℕ} {G : Matrix (Fin m) (Fin m) 𝕜}
    [RCLike 𝕜] (hG : G.IsHermitian) :
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2 ≤ frobSq (G - 1) := by
  rw [Aggregation.frobSq_eq_sum_sq]
  have h2 : ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2
      = ∑ i, ∑ j ∈ Finset.Ioi i, ‖(G - 1) i j‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ioi] at hj
    rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hj), sub_zero]
  rw [h2]
  refine Aggregation.two_mul_sum_upper_le _ (fun i j => sq_nonneg _) fun i j => ?_
  have happ : star ((G - 1) j i) = (G - 1) i j := by
    conv_rhs => rw [← (hG.sub Matrix.isHermitian_one).eq]
    rw [Matrix.conjTranspose_apply]
  rw [← happ, norm_star]

/-- **Sharp square-root block profile (Lemma 3.1, lower-bound part).**

For a positive semidefinite Hermitian matrix `G`, the spectral stability defect
dominates `h(E)`, where `E` is twice its strict-upper-triangle energy.  The theorem
does not require diagonal-one normalization. -/
theorem block_defect_sqrt {m : ℕ} {G : Matrix (Fin m) (Fin m) 𝕜} [RCLike 𝕜]
    (hG : G.PosSemidef) :
    sqrtProfile (2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2)
      ≤ ∑ i, StabilityRankTrace.Psi (hG.1.eigenvalues i) := by
  let E : ℝ := 2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2
  have hE0 : 0 ≤ E := by
    dsimp [E]
    positivity
  have heig0 : ∀ i, 0 ≤ hG.1.eigenvalues i := hG.eigenvalues_nonneg
  have hPsi : ∑ i, StabilityRankTrace.Psi (hG.1.eigenvalues i)
      = ∑ i, sqrtProfile ((hG.1.eigenvalues i - 1) ^ 2) :=
    Finset.sum_congr rfl fun i _ => Psi_eq_sqrtProfile_sq_sub_one (heig0 i)
  have hsum : sqrtProfile (∑ i, (hG.1.eigenvalues i - 1) ^ 2)
      ≤ ∑ i, sqrtProfile ((hG.1.eigenvalues i - 1) ^ 2) :=
    sqrtProfile_sum_le _ (fun i => sq_nonneg _)
  have hoff : E ≤ frobSq (G - 1) := offDiagEnergy_le_frobSq_sub_one hG.1
  have hfrob : frobSq (G - 1) = ∑ i, (hG.1.eigenvalues i - 1) ^ 2 :=
    frobSq_sub_one_eq_sum_sq_eigenvalues hG.1
  have hmono : sqrtProfile E ≤ sqrtProfile (∑ i, (hG.1.eigenvalues i - 1) ^ 2) := by
    apply sqrtProfile_monoOn hE0
      (by
        simp only [Set.mem_Ici]
        exact Finset.sum_nonneg fun i _ => sq_nonneg _)
    rwa [← hfrob]
  change sqrtProfile E ≤ _
  rw [hPsi]
  exact hmono.trans hsum

/-- Functional-calculus trace form of `block_defect_sqrt`. -/
theorem block_defect_sqrt_specMap {m : ℕ} {G : Matrix (Fin m) (Fin m) 𝕜}
    [RCLike 𝕜] (hG : G.PosSemidef) :
    sqrtProfile (2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2)
      ≤ rtrace (specMap hG.1 StabilityRankTrace.Psi) := by
  rw [StabilityRankTrace.rtrace_specMap_Psi]
  exact block_defect_sqrt hG

end Zeta23Ext.SqrtProfile
