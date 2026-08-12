/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentRetainedWithLoss
import Zeta23.ZeroSide.Final

/-!
# The central all-simple atom and inertia seam

The upstream zero-side block decomposes the enlarged-window matrix into all
on-line atoms plus an off-line remainder.  For the simple-zero theorem we must
split the on-line part once more: every simple on-line point is a normalized
rank-one atom, while the multiple on-line points join the off-line remainder.
The latter costs `s₂ + p` positive directions.

This file proves that algebra for the abstract upstream `ZeroBlockData` and
connects an explicit retained/discarded partition of the simple atoms to
`CurrentRetainedWithLoss.PrincipalCompression`.  The only selection premise
left is an equivalence which classifies which simple atoms lie in the central
window; no Gram identity, deletion, or inertia claim is hidden in it.
-/

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentCentralSimple

open Zeta23
open Zeta23.ZeroSide
open Zeta23Ext.CurrentRetainedWithLoss

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

namespace AllSimple

variable (D : ZeroSide.ZeroBlockData ι d)

/-- The unnormalized sum of the simple on-line rank-one atoms. -/
def simplePart : Matrix d d ℂ :=
  ∑ z ∈ D.S₁, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

/-- The unnormalized sum of the multiple on-line rank-one atoms. -/
def multiplePart : Matrix d d ℂ :=
  ∑ z ∈ D.S₂, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

lemma onPart_eq_simplePart_add_multiplePart :
    D.onPart = simplePart D + multiplePart D := by
  unfold ZeroSide.ZeroBlockData.onPart simplePart multiplePart
  rw [D.onLine_eq_S₁_union_S₂, sum_union D.disjoint_S₁_S₂]

lemma simplePart_posSemidef : (simplePart D).PosSemidef := by
  unfold simplePart
  refine posSemidef_sum _ fun z hz => ?_
  have hz' : D.σ z = z := by
    have hpair : D.σ z = z ∧ D.m z = 1 := by
      simpa only [ZeroSide.ZeroBlockData.S₁, mem_filter, mem_univ, true_and] using hz
    exact hpair.1
  exact ZeroSide.ZeroBlockData.posSemidef_smul_vecMulVec
    (D.star_v_of_onLine hz') (by positivity)

lemma multiplePart_posSemidef : (multiplePart D).PosSemidef := by
  unfold multiplePart
  refine posSemidef_sum _ fun z hz => ?_
  have hz' : D.σ z = z := by
    have hpair : D.σ z = z ∧ 2 ≤ D.m z := by
      simpa only [ZeroSide.ZeroBlockData.S₂, mem_filter, mem_univ, true_and] using hz
    exact hpair.1
  exact ZeroSide.ZeroBlockData.posSemidef_smul_vecMulVec
    (D.star_v_of_onLine hz') (by positivity)

lemma rank_multiplePart_le : (multiplePart D).rank ≤ D.s₂ := by
  unfold multiplePart ZeroSide.ZeroBlockData.s₂
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp

/-- Enumerate all simple atoms by `Fin s₁` and normalize them by `sqrt c`.
For the concrete zero block `c = a L²`. -/
def allSimpleAtoms (c : ℝ) : Matrix d (Fin (Fintype.card D.S₁)) ℂ := fun k j =>
  ((Real.sqrt c)⁻¹ : ℂ) * D.v ((Fintype.equivFin D.S₁).symm j) k

lemma allSimpleAtoms_gram {c : ℝ} (hc : 0 < c) :
    allSimpleAtoms D c * (allSimpleAtoms D c)ᴴ =
      ((c⁻¹ : ℝ) : ℂ) • simplePart D := by
  ext k l
  let e : Fin (Fintype.card D.S₁) ≃ D.S₁ := (Fintype.equivFin D.S₁).symm
  have hsum := Fintype.sum_equiv e
    (fun j => allSimpleAtoms D c k j * star (allSimpleAtoms D c l j))
    (fun z : D.S₁ => ((c⁻¹ : ℝ) : ℂ) * (D.v z k * D.v z l))
    (fun j => by
      have hzfix : D.σ (e j) = e j := by
        have hpair : D.σ (e j) = e j ∧ D.m (e j) = 1 := by
          simpa only [ZeroSide.ZeroBlockData.S₁, mem_filter, mem_univ, true_and] using (e j).2
        exact hpair.1
      have hv := congrFun (D.star_v_of_onLine hzfix) l
      simp only [Pi.star_apply, RCLike.star_def] at hv
      simp only [allSimpleAtoms, e, map_mul, RCLike.star_def, Complex.conj_inv,
        Complex.conj_ofReal, hv]
      push_cast
      have hsqrt : Real.sqrt c * Real.sqrt c = c := by nlinarith [Real.sq_sqrt hc.le]
      have hsqrtC : (((Real.sqrt c : ℝ) : ℂ) ^ 2) = (c : ℂ) := by
        norm_cast
        nlinarith
      field_simp [Real.sqrt_ne_zero'.mpr hc]
      rw [hsqrtC]
      ring)
  simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [hsum]
  unfold simplePart
  simp only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, smul_eq_mul]
  rw [Finset.sum_subtype D.S₁ (fun _ => Iff.rfl)]
  rw [Finset.mul_sum]
  refine sum_congr rfl fun z _ => ?_
  have hm : D.m z = 1 := by
    have hz' : D.σ z = z ∧ D.m z = 1 := by
      simpa only [ZeroSide.ZeroBlockData.S₁, mem_filter, mem_univ, true_and] using z.2
    exact hz'.2
  simp [hm]

lemma allSimpleAtoms_colSq_le {c : ℝ} (hc : 0 < c)
    (hnorm : ∀ z ∈ D.S₁, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    ∀ j, Zeta23Ext.StabilityRankTrace.colSq (allSimpleAtoms D c) j ≤ 1 := by
  intro j
  let z : D.S₁ := (Fintype.equivFin D.S₁).symm j
  have hz := hnorm z z.2
  unfold Zeta23Ext.StabilityRankTrace.colSq allSimpleAtoms
  simp only [norm_mul, norm_inv, Complex.norm_real, mul_pow]
  rw [← Finset.mul_sum]
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg c)]
  have hsqrt : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hc0 : c ≠ 0 := hc.ne'
  have hbound : (Real.sqrt c)⁻¹ ^ 2 * ∑ i, ‖D.v z i‖ ^ 2 ≤ 1 := by
    calc
      (Real.sqrt c)⁻¹ ^ 2 * ∑ i, ‖D.v z i‖ ^ 2 ≤
        (Real.sqrt c)⁻¹ ^ 2 * c := by gcongr
      _ = 1 := by
        field_simp [Real.sqrt_ne_zero'.mpr hc]
        nlinarith [hsqrt]
  simpa only [z] using hbound

/-- The correct remainder after keeping every simple on-line atom: multiple
on-line atoms are positive semidefinite and the upstream pair remainder has
positive index at most `p`. -/
def allSimpleQ (P : D.PairReps) (c : ℝ) : Matrix d d ℂ :=
  ((c⁻¹ : ℝ) : ℂ) • multiplePart D + D.blockQ c

lemma allSimpleQ_hermitian (P : D.PairReps) (c : ℝ) :
    (allSimpleQ D P c).IsHermitian :=
  (ZeroSide.ZeroBlockData.isHermitian_real_smul (multiplePart_posSemidef D).isHermitian _).add
    (D.blockQ_isHermitian c)

lemma allSimpleQ_posIndex_le (P : D.PairReps) {c : ℝ} (hc : 0 < c) :
    posIndex (allSimpleQ_hermitian D P c) ≤ D.s₂ + P.p := by
  have hmulti : (((c⁻¹ : ℝ) : ℂ) • multiplePart D).PosSemidef :=
    (multiplePart_posSemidef D).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))
  calc
    posIndex (allSimpleQ_hermitian D P c) ≤
        posIndex hmulti.isHermitian + posIndex (D.blockQ_isHermitian c) :=
      posIndex_add_le hmulti.isHermitian (D.blockQ_isHermitian c)
    _ = (((c⁻¹ : ℝ) : ℂ) • multiplePart D).rank +
        posIndex (D.blockQ_isHermitian c) := by
      rw [posIndex_eq_rank_of_posSemidef hmulti]
    _ ≤ D.s₂ + P.p := Nat.add_le_add
      ((rank_smul_of_ne_zero (multiplePart D) (by exact_mod_cast inv_ne_zero hc.ne')).le.trans
        (rank_multiplePart_le D))
      (D.posIndex_blockQ_le P hc)

lemma allSimple_decomposition (P : D.PairReps) {c : ℝ} (hc : 0 < c) :
    ((c⁻¹ : ℝ) : ℂ) • D.blockA =
      allSimpleAtoms D c * (allSimpleAtoms D c)ᴴ + allSimpleQ D P c := by
  rw [allSimpleAtoms_gram D hc]
  rw [← D.blockP_add_blockQ c]
  unfold allSimpleQ ZeroSide.ZeroBlockData.blockP
  rw [onPart_eq_simplePart_add_multiplePart D, smul_add]
  abel

end AllSimple

/-! ## The exact finite selection seam -/

/-- The sole finite-selection premise: an enumeration of the simple atoms is
partitioned into retained central columns and discarded boundary columns.
The Gram identity prevents duplication or omission, while `count_split`
records the cardinality statement needed by deletion bookkeeping. -/
structure CentralSimpleSelection {d s1 : ℕ}
    (A : Matrix (Fin d) (Fin s1) ℂ) (r deleted : ℕ) where
  V : Matrix (Fin d) (Fin r) ℂ
  W : Matrix (Fin d) (Fin deleted) ℂ
  gram_split : A * Aᴴ = V * Vᴴ + W * Wᴴ
  count_split : r + deleted = s1
  retained_col_le : ∀ j, Zeta23Ext.StabilityRankTrace.colSq V j ≤ 1

/-- Reindexing all columns by a disjoint sum automatically gives the exact
Gram split.  Thus a caller does not need to assume any matrix identity once
it supplies a genuine retained/discarded equivalence. -/
def CentralSimpleSelection.ofEquiv
    {d s1 r deleted : ℕ} (A : Matrix (Fin d) (Fin s1) ℂ)
    (e : Fin r ⊕ Fin deleted ≃ Fin s1)
    (hcol : ∀ j, Zeta23Ext.StabilityRankTrace.colSq A j ≤ 1) :
    CentralSimpleSelection A r deleted where
  V i j := A i (e (Sum.inl j))
  W i j := A i (e (Sum.inr j))
  gram_split := by
    ext i j
    simp only [Matrix.mul_apply, conjTranspose_apply]
    have hsum := Fintype.sum_equiv e
      (fun x => A i (e x) * star (A j (e x)))
      (fun k => A i k * star (A j k)) (fun _ => rfl)
    rw [Fintype.sum_sum_type] at hsum
    exact hsum.symm
  count_split := by
    simpa using Fintype.card_congr e
  retained_col_le j := hcol (e (Sum.inl j))

/-- Package the central selection with the all-simple inertia remainder. -/
def CentralSimpleSelection.compression
    {d s1 r deleted : ℕ} {A : Matrix (Fin d) (Fin s1) ℂ}
    (S : CentralSimpleSelection A r deleted) (Qoff : Matrix (Fin d) (Fin d) ℂ)
    (hQoff : Qoff.IsHermitian) : PrincipalCompression d r deleted where
  V := S.V
  W := S.W
  Qoff := Qoff
  Qoff_hermitian := hQoff

lemma CentralSimpleSelection.retained_decomposition
    {d s1 s2 p N r deleted : ℕ} {A : Matrix (Fin d) (Fin s1) ℂ}
    (S : CentralSimpleSelection A r deleted)
    (Qoff : Matrix (Fin d) (Fin d) ℂ) (hQoff : Qoff.IsHermitian)
    (hpos : posIndex hQoff ≤ s2 + p)
    (hcount : s1 + 2 * s2 + 2 * p ≤ N) :
    LossyRetainedDecomposition (deleted + (s2 + p)) (N : ℝ)
      (2 * (deleted : ℝ)) S.V (S.compression Qoff hQoff).remainder := by
  apply (S.compression Qoff hQoff).toLossyRetainedDecomposition
    (s1 := s1) (s2 := 0) S.retained_col_le hpos S.count_split
  omega

/-- Exact central matrix identity.  This is the bridge needed to transfer
trace/Frobenius estimates for the enlarged-window matrix to the retained
moment interface; only analytic tail estimates remain after this lemma. -/
lemma CentralSimpleSelection.matrix_identity
    {d s1 r deleted : ℕ} {A : Matrix (Fin d) (Fin s1) ℂ}
    (S : CentralSimpleSelection A r deleted)
    (Qoff : Matrix (Fin d) (Fin d) ℂ) (hQoff : Qoff.IsHermitian)
    {M : Matrix (Fin d) (Fin d) ℂ} (hM : M = A * Aᴴ + Qoff) :
    M = S.V * S.Vᴴ + (S.compression Qoff hQoff).remainder := by
  rw [hM, S.gram_split]
  simp only [PrincipalCompression.remainder]
  abel

/-! ## Concrete upstream specialization and the remaining premise -/

/-- All normalized simple atoms in the concrete enlarged zero window. -/
def concreteAllSimpleAtoms (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Matrix (Fin (P.d T))
      (Fin (Fintype.card (ZeroSide.blockData Z T P hconj).S₁)) ℂ :=
  AllSimple.allSimpleAtoms (ZeroSide.blockData Z T P hconj) (P.a T * P.L T ^ 2)

/-- The concrete multiple-on-line plus off-line inertia remainder. -/
def concreteAllSimpleQ (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  AllSimple.allSimpleQ (ZeroSide.blockData Z T P hconj)
    (ZeroSide.mkPairReps Z T _ (ZeroSide.evalVec_reflect hconj))
    (P.a T * P.L T ^ 2)

lemma concreteAllSimpleQ_hermitian (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    (concreteAllSimpleQ Z P T hconj).IsHermitian :=
  AllSimple.allSimpleQ_hermitian _ _ _

/-- Upstream `Az` is exactly the Gram matrix of all simple on-line atoms plus
the multiple/off-line inertia remainder. -/
theorem hat_Az_allSimple_decomposition
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    P.hat T (Z.Az P T) =
      concreteAllSimpleAtoms Z P T hconj *
        (concreteAllSimpleAtoms Z P T hconj)ᴴ +
      concreteAllSimpleQ Z P T hconj := by
  rw [ZeroSide.hat_eq, ZeroSide.Az_eq_blockA Z T P hconj]
  exact AllSimple.allSimple_decomposition _ _ hc

theorem concreteAllSimpleQ_posIndex_le
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    posIndex (concreteAllSimpleQ_hermitian Z P T hconj) ≤ Z.s2 T + Z.p T := by
  have h := AllSimple.allSimpleQ_posIndex_le
    (ZeroSide.blockData Z T P hconj)
    (ZeroSide.mkPairReps Z T _ (ZeroSide.evalVec_reflect hconj)) hc
  rw [ZeroSide.s2_eq_mk Z T _ (ZeroSide.evalVec_reflect hconj),
    ZeroSide.p_eq_mk Z T _ (ZeroSide.evalVec_reflect hconj)]
  change posIndex (AllSimple.allSimpleQ_hermitian
    (ZeroSide.blockData Z T P hconj)
    (ZeroSide.mkPairReps Z T _ (ZeroSide.evalVec_reflect hconj))
    (P.a T * P.L T ^ 2)) ≤
      (ZeroSide.mkData Z T (ZeroSide.evalVec Z T P)
        (ZeroSide.evalVec_reflect hconj)).s₂ +
      (ZeroSide.mkPairReps Z T _ (ZeroSide.evalVec_reflect hconj)).p
  simpa only [ZeroSide.blockData] using h

/-- The upstream Poisson estimate makes every concrete simple column have
squared norm at most one. -/
theorem concreteAllSimpleAtoms_colSq_le
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    ∀ j, Zeta23Ext.StabilityRankTrace.colSq
      (concreteAllSimpleAtoms Z P T hconj) j ≤ 1 := by
  apply AllSimple.allSimpleAtoms_colSq_le _ hc
  intro z hz
  apply ZeroSide.sum_normSq_v_le Z T P hconj hreal hPois z
  rw [ZeroSide.ZeroBlockData.mem_onLine]
  have hpair : (ZeroSide.blockData Z T P hconj).σ z = z ∧
      (ZeroSide.blockData Z T P hconj).m z = 1 := by
    simpa only [ZeroSide.ZeroBlockData.S₁, mem_filter, mem_univ, true_and] using hz
  exact hpair.1

/-- The strongest finite premise needed to select central simple atoms.  The
equivalence partitions every simple atom of the enlarged window; its two
membership fields classify the two sides by ordinate.  The count field is
the remaining bridge to the abstract `N0s` definition.

Unlike `ConcreteCentralSelection`, this structure contains no assumed Gram
identity: `toSelection` proves that identity from `e`. -/
structure ConcreteCentralReindexing (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) where
  r : ℕ
  deleted : ℕ
  e : Fin r ⊕ Fin deleted ≃ (ZeroSide.blockData Z T P hconj).S₁
  retained_mem : ∀ j,
    T < (((e (Sum.inl j)).1 : ℂ).im) ∧
      (((e (Sum.inl j)).1 : ℂ).im) ≤ 2 * T
  discarded_not_mem : ∀ j, ¬(
    T < (((e (Sum.inr j)).1 : ℂ).im) ∧
      (((e (Sum.inr j)).1 : ℂ).im) ≤ 2 * T)
  retained_count : r = Z.N0s T (2 * T)

namespace ConcreteCentralReindexing

variable {Z : ZeroConfig} {P : Params} {T : ℝ}
  {hconj : ZeroSide.PhiHatConj T P}

/-- Turn a semantic atom partition into the matrix-level selection. -/
def toSelection (S : ConcreteCentralReindexing Z P T hconj)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    CentralSimpleSelection (concreteAllSimpleAtoms Z P T hconj)
      S.r S.deleted :=
  CentralSimpleSelection.ofEquiv _
    (S.e.trans (Fintype.equivFin _))
    (concreteAllSimpleAtoms_colSq_le Z P T hconj hreal hPois hc)

end ConcreteCentralReindexing

/-- Matrix-level finite selection obligation for the concrete zero block.
The Gram and count fields say that all simple atoms split into retained and
discarded columns with the required cardinalities.  A later Gram/ordinate
producer must still identify the retained columns with the simple zeros in
`(T,2T]`; that semantic identification is deliberately not claimed here.
No inertia, matrix decomposition, or count inequality is assumed. -/
structure ConcreteCentralSelection (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) (c : ℝ) where
  r : ℕ
  deleted : ℕ
  selection : CentralSimpleSelection
    (AllSimple.allSimpleAtoms (ZeroSide.blockData Z T P hconj) c) r deleted
  retained_count : r = Z.N0s T (2 * T)
  boundary_count : deleted = Z.s1 T - Z.N0s T (2 * T)

/-- A semantic reindexing canonically supplies the weaker matrix-level
selection package used by the retained-moment interface. -/
def ConcreteCentralReindexing.toCentralSelection
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    {hconj : ZeroSide.PhiHatConj T P}
    (S : ConcreteCentralReindexing Z P T hconj)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    ConcreteCentralSelection Z P T hconj (P.a T * P.L T ^ 2) where
  r := S.r
  deleted := S.deleted
  selection := S.toSelection hreal hPois hc
  retained_count := S.retained_count
  boundary_count := by
    have hs1 : Fintype.card (ZeroSide.blockData Z T P hconj).S₁ = Z.s1 T := by
      rw [ZeroSide.s1_eq_mk Z T _ (ZeroSide.evalVec_reflect hconj)]
      change Fintype.card ↥(ZeroSide.mkData Z T (ZeroSide.evalVec Z T P)
        (ZeroSide.evalVec_reflect hconj)).S₁ =
          #(ZeroSide.mkData Z T (ZeroSide.evalVec Z T P)
            (ZeroSide.evalVec_reflect hconj)).S₁
      exact Fintype.card_coe _
    have hsplit := (S.toSelection hreal hPois hc).count_split
    have hret := S.retained_count
    rw [hs1] at hsplit
    omega

namespace ConcreteCentralSelection

variable {Z : ZeroConfig} {P : Params} {T : ℝ}
  {hconj : ZeroSide.PhiHatConj T P} {c : ℝ}

/-- A concrete central selection feeds the corrected principal-compression
and deletion-loss interface using the upstream exact zero count. -/
theorem lossyRetained (S : ConcreteCentralSelection Z P T hconj c)
    (hc : 0 < c) (hc_eq : c = P.a T * P.L T ^ 2) :
    LossyRetainedDecomposition
      (S.deleted + (Z.s2 T + Z.p T)) (Z.NIprime T : ℝ)
      (2 * (S.deleted : ℝ)) S.selection.V
      (S.selection.compression (concreteAllSimpleQ Z P T hconj)
        (concreteAllSimpleQ_hermitian Z P T hconj)).remainder := by
  subst c
  have hs1 : Fintype.card (ZeroSide.blockData Z T P hconj).S₁ = Z.s1 T := by
    rw [ZeroSide.s1_eq_mk Z T _ (ZeroSide.evalVec_reflect hconj)]
    change Fintype.card ↥(ZeroSide.mkData Z T (ZeroSide.evalVec Z T P)
      (ZeroSide.evalVec_reflect hconj)).S₁ =
        #(ZeroSide.mkData Z T (ZeroSide.evalVec Z T P)
          (ZeroSide.evalVec_reflect hconj)).S₁
    exact Fintype.card_coe _
  have hcount := ZeroSide.s1_add_two_s2_add_two_p_le_NIprime Z T
  rw [← hs1] at hcount
  exact S.selection.retained_decomposition _ _
    (concreteAllSimpleQ_posIndex_le Z P T hconj hc) hcount

/-- Exact retained matrix identity in concrete hat units. -/
theorem hatAz_identity (S : ConcreteCentralSelection Z P T hconj c)
    (hc : 0 < c) (hc_eq : c = P.a T * P.L T ^ 2) :
    P.hat T (Z.Az P T) = S.selection.V * S.selection.Vᴴ +
      (S.selection.compression (concreteAllSimpleQ Z P T hconj)
        (concreteAllSimpleQ_hermitian Z P T hconj)).remainder := by
  subst c
  apply S.selection.matrix_identity _ _
  exact hat_Az_allSimple_decomposition Z P T hconj hc

end ConcreteCentralSelection

/-- The exact analytic tail/moment obligation left after central selection.
The matrix is the enlarged-window `Az`, not `Gz`; estimates for `Gz` may be
transferred through the already-proved upstream `Ez` tail bounds. -/
structure CentralAzMomentPremise
    (Z : ZeroConfig) (P : Params) (T N R₁ R₂ : ℝ) : Prop where
  trace_lower : N - R₁ ≤ RHLinalg.rtrace (P.hat T (Z.Az P T))
  frobenius_upper : RHLinalg.frobSq (P.hat T (Z.Az P T)) ≤
    (2 - Current.Hcert) * N + R₂

/-- The defining tail identity, in hat units. -/
lemma hat_Gz_eq_hat_Az_add_hat_Ez
    (Z : ZeroConfig) (P : Params) (T : ℝ) :
    P.hat T (Z.Gz P T) =
      P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
  rw [← Zeta23.Assembly.hat_add]
  congr 1
  simp [ZeroConfig.Ez]

/-- Transfer separate trace and Frobenius estimates from the full zero-side
matrix `Gz` to the enlarged finite matrix `Az`.  The only extra inputs are a
common nonnegative tail bound for `|tr Ez|` and `‖Ez‖_F`.  The displayed
remainder is exact: the Frobenius loss is
`2 * sqrt (frobSq Ghat) * B + B²`.

This theorem intentionally does not absorb the difference between the
central count and `NIprime`; callers must rebase `N`, or charge that count
difference in `R₁` and `R₂`, explicitly. -/
theorem CentralAzMomentPremise.ofGzTail
    (Z : ZeroConfig) (P : Params) (T N R₁ R₂ B : ℝ)
    (hGtrace : N - R₁ ≤ RHLinalg.rtrace (P.hat T (Z.Gz P T)))
    (hGfrob : RHLinalg.frobSq (P.hat T (Z.Gz P T)) ≤
      (2 - Current.Hcert) * N + R₂)
    (hB : 0 ≤ B)
    (htrE : |RHLinalg.rtrace (P.hat T (Z.Ez P T))| ≤ B)
    (hfrE : RHLinalg.frobSq (P.hat T (Z.Ez P T)) ≤ B ^ 2) :
    CentralAzMomentPremise Z P T N (R₁ + B)
      (R₂ + 2 * Real.sqrt (RHLinalg.frobSq (P.hat T (Z.Gz P T))) * B + B ^ 2) := by
  let Ghat := P.hat T (Z.Gz P T)
  let Ahat := P.hat T (Z.Az P T)
  let Ehat := P.hat T (Z.Ez P T)
  have hGAE : Ghat = Ahat + Ehat := hat_Gz_eq_hat_Az_add_hat_Ez Z P T
  have hA : Ahat = Ghat - Ehat := by rw [hGAE]; abel
  have htr : RHLinalg.rtrace Ahat =
      RHLinalg.rtrace Ghat - RHLinalg.rtrace Ehat := by
    rw [hA, RHLinalg.rtrace_sub]
  have htrE' : RHLinalg.rtrace Ehat ≤ B := (le_abs_self _).trans htrE
  have hsqrtE : Real.sqrt (RHLinalg.frobSq Ehat) ≤ B :=
    Real.sqrt_le_iff.mpr ⟨hB, hfrE⟩
  have hfrA : RHLinalg.frobSq Ahat ≤
      (Real.sqrt (RHLinalg.frobSq Ghat) + B) ^ 2 := by
    rw [hA]
    refine (Zeta23.Assembly.frobSq_sub_le Ghat Ehat).trans ?_
    gcongr
  have hGsq : Real.sqrt (RHLinalg.frobSq Ghat) ^ 2 =
      RHLinalg.frobSq Ghat :=
    Real.sq_sqrt (Zeta23.Assembly.frobSq_nonneg _)
  constructor
  · change N - (R₁ + B) ≤ RHLinalg.rtrace Ahat
    change N - R₁ ≤ RHLinalg.rtrace Ghat at hGtrace
    linarith
  · change RHLinalg.frobSq Ahat ≤
      (2 - Current.Hcert) * N +
        (R₂ + 2 * Real.sqrt (RHLinalg.frobSq Ghat) * B + B ^ 2)
    change RHLinalg.frobSq Ghat ≤ (2 - Current.Hcert) * N + R₂ at hGfrob
    nlinarith

end Zeta23Ext.CurrentCentralSimple
