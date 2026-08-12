/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentCentralSimple
import Zeta23Ext.CurrentAnalyticInstantiation

/-!
# Canonical central-simple selection

This module removes the finite selection premise from
`CurrentCentralSimple`.  It partitions the concrete enlarged-window simple
atoms by the central ordinate predicate, proves that the retained subtype has
cardinality `N0s T (2*T)`, and obtains the matrix Gram split from the canonical
sum-complement equivalence.
-/

noncomputable section

open Matrix Finset Set RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentCentralSelection

open Zeta23
open Zeta23.ZeroSide
open Zeta23Ext.CurrentCentralSimple
open Zeta23Ext.CurrentRetainedWithLoss

abbrev ConcreteS1 (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :=
  (ZeroSide.blockData Z T P hconj).S₁

/-- Central-window membership for a concrete enlarged-window simple atom. -/
def IsCentralAtom (T : ℝ) {Z : ZeroConfig} {P : Params}
    {hconj : ZeroSide.PhiHatConj T P}
    (z : ConcreteS1 Z P T hconj) : Prop :=
  T < ((z.1.1 : ℂ).im) ∧ ((z.1.1 : ℂ).im) ≤ 2 * T

abbrev RetainedAtom (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :=
  {z : ConcreteS1 Z P T hconj // IsCentralAtom T z}

abbrev BoundaryAtom (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :=
  {z : ConcreteS1 Z P T hconj // ¬ IsCentralAtom T z}

noncomputable instance retainedAtomFintype
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fintype (RetainedAtom Z P T hconj) := Fintype.ofFinite _

noncomputable instance boundaryAtomFintype
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fintype (BoundaryAtom Z P T hconj) := Fintype.ofFinite _

/-- A retained enlarged-window atom determines a central simple critical-line
zero. -/
def retainedAtomToCentralZero
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    RetainedAtom Z P T hconj ≃
      ↥(Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple) where
  toFun z := ⟨z.1.1.1, by
    have hzS1 :
        (ZeroSide.blockData Z T P hconj).σ z.1.1 = z.1.1 ∧
          (ZeroSide.blockData Z T P hconj).m z.1.1 = 1 := by
      simpa only [ZeroSide.ZeroBlockData.S₁, mem_filter, Finset.mem_univ, true_and]
        using z.1.2
    have hre : (z.1.1.1 : ℂ).re = 1 / 2 :=
      (ZeroSide.mkData_σ_eq_iff Z T _ (ZeroSide.evalVec_reflect hconj) z.1.1).mp hzS1.1
    have hm : Z.mult (z.1.1.1 : ℂ) = 1 := hzS1.2
    have hcarrier : (z.1.1.1 : ℂ) ∈ Z.carrier := by
      have hzI : (z.1.1.1 : ℂ) ∈ Z.ZIprime T :=
        (ZeroSide.mem_ZI Z T).mp z.1.1.2
      exact (ZeroSide.mem_ZIprime_iff Z T).mp hzI |>.1
    exact ⟨⟨⟨hcarrier, z.2⟩, hre⟩, hm⟩⟩
  invFun z := by
    have hD0 : 0 ≤ D0 T := Zeta23.Assembly.D0_nonneg T
    have hzwin : (z.1 : ℂ) ∈ Z.window T (2 * T) := z.2.1.1
    have hzI : (z.1 : ℂ) ∈ Z.ZIprime T := by
      rw [ZeroSide.mem_ZIprime_iff]
      exact ⟨hzwin.1, by linarith [hzwin.2.1], by linarith [hzwin.2.2]⟩
    let zi : ZeroSide.ZI Z T := ⟨z.1, (ZeroSide.mem_ZI Z T).mpr hzI⟩
    have hzS1 : zi ∈ (ZeroSide.blockData Z T P hconj).S₁ := by
      rw [ZeroSide.ZeroBlockData.S₁, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (ZeroSide.mkData_σ_eq_iff Z T _
        (ZeroSide.evalVec_reflect hconj) zi).mpr z.2.1.2, z.2.2⟩
    exact ⟨⟨zi, hzS1⟩, z.2.1.1.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

/-- The canonical retained atom count is exactly the desired simple-zero
count, not merely bounded by it. -/
theorem card_retainedAtom
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fintype.card (RetainedAtom Z P T hconj) = Z.N0s T (2 * T) := by
  let s : Set ℂ := Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple
  have hs : s.Finite := (Z.window_finite T (2 * T)).subset (by
    intro z hz
    exact hz.1.1)
  letI : Fintype ↥s := hs.fintype
  calc
    Fintype.card (RetainedAtom Z P T hconj) = Fintype.card ↥s :=
      Fintype.card_congr (retainedAtomToCentralZero Z P T hconj)
    _ = s.ncard := Set.fintypeCard_eq_ncard s
    _ = Z.N0s T (2 * T) := rfl

/-- Ordinate is injective on retained critical-line atoms. -/
theorem retainedAtom_ordinate_injective
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Function.Injective
      (fun z : RetainedAtom Z P T hconj => ((z.1.1.1 : ℂ).im)) := by
  intro z w him
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Complex.ext
  · have hz := (retainedAtomToCentralZero Z P T hconj z).2.1.2
    have hw := (retainedAtomToCentralZero Z P T hconj w).2.1.2
    change (z.1.1.1 : ℂ).re = 1 / 2 at hz
    change (w.1.1.1 : ℂ).re = 1 / 2 at hw
    linarith
  · exact him

private structure OrderedRetainedAtom
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) where
  val : RetainedAtom Z P T hconj

private noncomputable instance
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fintype (OrderedRetainedAtom Z P T hconj) :=
  Fintype.ofEquiv (RetainedAtom Z P T hconj)
    { toFun := fun z => ⟨z⟩
      invFun := fun z => z.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private noncomputable instance
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    LinearOrder (OrderedRetainedAtom Z P T hconj) :=
  LinearOrder.lift'
    (fun z : OrderedRetainedAtom Z P T hconj => ((z.val.1.1.1 : ℂ).im))
    fun z w h => by
      cases z
      cases w
      congr
      exact retainedAtom_ordinate_injective Z P T hconj h

private def orderedRetainedAtomEquiv
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    OrderedRetainedAtom Z P T hconj ≃ RetainedAtom Z P T hconj where
  toFun := fun z => z.val
  invFun := fun z => ⟨z⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Increasing-ordinate enumeration of the retained atoms. -/
noncomputable def orderedRetainedEquiv
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fin (Fintype.card (RetainedAtom Z P T hconj)) ≃
      RetainedAtom Z P T hconj :=
  let hcard : Fintype.card (OrderedRetainedAtom Z P T hconj) =
      Fintype.card (RetainedAtom Z P T hconj) :=
    Fintype.card_congr (orderedRetainedAtomEquiv Z P T hconj)
  (Fintype.orderIsoFinOfCardEq
    (OrderedRetainedAtom Z P T hconj) hcard).toEquiv.trans
      (orderedRetainedAtomEquiv Z P T hconj)

theorem orderedRetainedEquiv_ordinate_strictMono
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    StrictMono (fun j =>
      ((((orderedRetainedEquiv Z P T hconj j).1.1 : ZeroSide.ZI Z T) : ℂ).im)) := by
  intro i j hij
  let hcard : Fintype.card (OrderedRetainedAtom Z P T hconj) =
      Fintype.card (RetainedAtom Z P T hconj) :=
    Fintype.card_congr (orderedRetainedAtomEquiv Z P T hconj)
  have hh := (Fintype.orderIsoFinOfCardEq
    (OrderedRetainedAtom Z P T hconj) hcard).strictMono hij
  exact hh

/-- Canonical partition equivalence: no caller-supplied finite selection or
Gram identity remains. -/
def centralBoundaryEquiv
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fin (Fintype.card (RetainedAtom Z P T hconj)) ⊕
        Fin (Fintype.card (BoundaryAtom Z P T hconj)) ≃
      ConcreteS1 Z P T hconj := by
  classical
  exact
    (Equiv.sumCongr (orderedRetainedEquiv Z P T hconj)
      (Fintype.equivFin _).symm).trans
      (Equiv.sumCompl (IsCentralAtom T))

@[simp] theorem centralBoundaryEquiv_inl
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (j : Fin (Fintype.card (RetainedAtom Z P T hconj))) :
    centralBoundaryEquiv Z P T hconj (Sum.inl j) =
      (orderedRetainedEquiv Z P T hconj j).1 := by
  simp [centralBoundaryEquiv]

/-- The canonical semantic reindexing required by `CurrentCentralSimple`. -/
def canonicalReindexing
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    ConcreteCentralReindexing Z P T hconj where
  r := Fintype.card (RetainedAtom Z P T hconj)
  deleted := Fintype.card (BoundaryAtom Z P T hconj)
  e := centralBoundaryEquiv Z P T hconj
  retained_mem j := (orderedRetainedEquiv Z P T hconj j).2
  discarded_not_mem j := ((Fintype.equivFin _).symm j).2
  retained_count := card_retainedAtom Z P T hconj

/-- Fully constructed central selection, with no finite selection premise. -/
def canonicalCentralSelection
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    ConcreteCentralSelection Z P T hconj (P.a T * P.L T ^ 2) :=
  (canonicalReindexing Z P T hconj).toCentralSelection hreal hPois hc

/-- Ordered retained zeros matching the retained columns of
`canonicalCentralSelection`.  Its ordinate normalization must subsequently
use `scaledOrdinate P T`, not the global `l T` scale. -/
def canonicalRetainedZeroData
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hr : 0 < Fintype.card (RetainedAtom Z P T hconj)) :
    CurrentAnalyticInstantiation.RetainedZeroData Z T
      (Fintype.card (RetainedAtom Z P T hconj)) where
  r_pos := hr
  rho j := (orderedRetainedEquiv Z P T hconj j).1.1
  dyadic j := (orderedRetainedEquiv Z P T hconj j).2
  onLine j := (retainedAtomToCentralZero Z P T hconj
    (orderedRetainedEquiv Z P T hconj j)).2.1.2
  simple j := (retainedAtomToCentralZero Z P T hconj
    (orderedRetainedEquiv Z P T hconj j)).2.2
  ordinate_strictMono := orderedRetainedEquiv_ordinate_strictMono Z P T hconj

/-- The canonical selection matrix is literally the upstream retained atom
matrix in increasing-ordinate order. -/
theorem canonicalCentralSelection_V_eq_retainedV
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (hr : 0 < Fintype.card (RetainedAtom Z P T hconj)) :
    (canonicalCentralSelection Z P T hconj hreal hPois hc).selection.V =
      (canonicalRetainedZeroData Z P T hconj hr).V P := by
  ext i j
  have hcancel :
      (Fintype.equivFin (ConcreteS1 Z P T hconj)).symm
          (((centralBoundaryEquiv Z P T hconj).trans
            (Fintype.equivFin (ConcreteS1 Z P T hconj))) (Sum.inl j)) =
        (orderedRetainedEquiv Z P T hconj j).1 := by
    rw [Equiv.trans_apply, Equiv.symm_apply_apply]
    exact centralBoundaryEquiv_inl Z P T hconj j
  simp only [canonicalCentralSelection, ConcreteCentralReindexing.toCentralSelection,
    ConcreteCentralReindexing.toSelection, CentralSimpleSelection.ofEquiv,
    canonicalReindexing, concreteAllSimpleAtoms, AllSimple.allSimpleAtoms,
    canonicalRetainedZeroData,
    CurrentAnalyticInstantiation.RetainedZeroData.V]
  rw [hcancel]
  simp [ZeroSide.blockData, ZeroSide.evalVec]
  ring

/-- Correct `P.L T`-scaled coordinate for the canonical retained atoms. -/
def canonicalScaledY
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hr : 0 < Fintype.card (RetainedAtom Z P T hconj))
    (j : Fin (Fintype.card (RetainedAtom Z P T hconj))) : ℝ :=
  scaledOrdinate P T
    ((((canonicalRetainedZeroData Z P T hconj hr).rho j :
      ZeroSide.ZI Z T) : ℂ).im)

theorem canonicalScaledY_strictMono
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hr : 0 < Fintype.card (RetainedAtom Z P T hconj))
    (hL : 0 < P.L T) :
    StrictMono (canonicalScaledY Z P T hconj hr) :=
  (scaledOrdinate_strictMono hL).comp
    (canonicalRetainedZeroData Z P T hconj hr).ordinate_strictMono

/-- Span of the retained scaled ordinates is controlled by the actual
parameter length `P.L T`. -/
theorem canonicalScaledY_span_le
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hr : 0 < Fintype.card (RetainedAtom Z P T hconj))
    (hL : 0 ≤ P.L T) :
    canonicalScaledY Z P T hconj hr
        ⟨Fintype.card (RetainedAtom Z P T hconj) - 1, by omega⟩ -
      canonicalScaledY Z P T hconj hr ⟨0, hr⟩ ≤
        scaledWindowLength P T := by
  apply scaledOrdinate_sub_le_windowLength hL
  · exact (canonicalRetainedZeroData Z P T hconj hr).dyadic ⟨0, hr⟩ |>.1.le
  · exact (canonicalRetainedZeroData Z P T hconj hr).dyadic
      ⟨Fintype.card (RetainedAtom Z P T hconj) - 1, by omega⟩ |>.2

@[simp] theorem canonicalCentralSelection_r
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    (canonicalCentralSelection Z P T hconj hreal hPois hc).r =
      Z.N0s T (2 * T) :=
  card_retainedAtom Z P T hconj

@[simp] theorem canonicalCentralSelection_deleted
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    (canonicalCentralSelection Z P T hconj hreal hPois hc).deleted =
      Z.s1 T - Z.N0s T (2 * T) :=
  (canonicalCentralSelection Z P T hconj hreal hPois hc).boundary_count

/-- The exact deletion count is bounded above by the enlarged-window boundary
count `NII`.  This direction is crucial: it is what makes the charged
deletion loss asymptotically negligible. -/
theorem canonical_deleted_le_NII
    (Z : ZeroConfig) (P : Params) {T : ℝ} (hT : 0 ≤ T)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    (canonicalCentralSelection Z P T hconj hreal hPois hc).deleted ≤
      Zeta23.Assembly.NII Z T := by
  rw [canonicalCentralSelection_deleted]
  have hs1 := Zeta23.Assembly.s1_le Z hT
  omega

/-- Pointwise real deletion loss bound used by the final asymptotic
assembler. -/
theorem canonical_countLoss_le_two_NII
    (Z : ZeroConfig) (P : Params) {T : ℝ} (hT : 0 ≤ T)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    2 * ((canonicalCentralSelection Z P T hconj hreal hPois hc).deleted : ℝ) ≤
      2 * (Zeta23.Assembly.NII Z T : ℝ) := by
  exact_mod_cast Nat.mul_le_mul_left 2
    (canonical_deleted_le_NII Z P hT hconj hreal hPois hc)

/-- The canonical retained decomposition.  Its deletion loss is exactly twice
the number of enlarged-window simple atoms outside the central window. -/
theorem canonical_lossyRetained
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    let S := canonicalCentralSelection Z P T hconj hreal hPois hc
    LossyRetainedDecomposition
      (S.deleted + (Z.s2 T + Z.p T)) (Z.NIprime T : ℝ)
      (2 * (S.deleted : ℝ)) S.selection.V
      (S.selection.compression (concreteAllSimpleQ Z P T hconj)
        (concreteAllSimpleQ_hermitian Z P T hconj)).remainder := by
  dsimp only
  exact ConcreteCentralSelection.lossyRetained _ hc rfl

/-- Moment data for the canonical compression from honest `Az` moments. -/
theorem canonical_lossyMomentData
    (Z : ZeroConfig) (P : Params) (T R₁ R₂ : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (hm : CentralAzMomentPremise Z P T (Z.NIprime T : ℝ) R₁ R₂) :
    let S := canonicalCentralSelection Z P T hconj hreal hPois hc
    LossyMomentData
      (S.deleted + (Z.s2 T + Z.p T)) (Z.NIprime T : ℝ) R₁ R₂
      (2 * (S.deleted : ℝ)) S.selection.V
      (S.selection.compression (concreteAllSimpleQ Z P T hconj)
        (concreteAllSimpleQ_hermitian Z P T hconj)).remainder := by
  dsimp only
  let S := canonicalCentralSelection Z P T hconj hreal hPois hc
  have hret := canonical_lossyRetained Z P T hconj hreal hPois hc
  have hid := ConcreteCentralSelection.hatAz_identity S hc rfl
  exact
    { hret with
      trace_lower := by simpa only [hid] using hm.trace_lower
      frobenius_upper := by simpa only [hid] using hm.frobenius_upper }

end Zeta23Ext.CurrentCentralSelection
