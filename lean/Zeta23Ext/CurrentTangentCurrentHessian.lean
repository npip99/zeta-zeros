/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentCurrentAssembly

/-!
# Current tangent Hessian assembly

The first theorem transports a checked wide range row directly to every real
point in the payload's closed midpoint/radius box.  This deliberately avoids
rounding such a point back to the original discrete leaf: the exact upper
face belongs to the adjacent half-open grid cell, while the wide range format
was designed to cover that closed face semantically.
-/

noncomputable section

open Set Matrix
open scoped BigOperators

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentHessian

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay
open Zeta23Ext.VerifiedCertificate.CurrentTangent
open Zeta23Ext.VerifiedCertificate.CurrentTangent.Local
open Zeta23Ext.VerifiedCertificate.CurrentTangent.Range

private lemma payload_coordinate_bounds {p : TangentPayload 6} {box : Box 6}
    (hp : p.check (grid := 4000) box = true) {x : Fin 6 → ℝ}
    (hx : InBox p x) (k : Fin 6) :
    (box.lo k : ℝ) / 4000 ≤ x k ∧
      x k ≤ ((box.hi k : ℕ) + 1 : ℝ) / 4000 := by
  rw [TangentPayload.check, Bool.and_eq_true] at hp
  have hf := of_decide_eq_true hp.1
  have hc := congrArg (fun z : ℚ => (z : ℝ)) (hf.2.1 k)
  have hr := congrArg (fun z : ℚ => (z : ℝ)) (hf.2.2.1 k)
  push_cast at hc hr
  have hloEq : (p.center k : ℝ) - p.radius k = (box.lo k : ℝ) / 4000 := by
    rw [hc, hr]
    norm_num
    ring
  have hhiEq : (p.center k : ℝ) + p.radius k =
      ((box.hi k : ℕ) + 1 : ℝ) / 4000 := by
    rw [hc, hr]
    norm_num
    ring
  have hxk := hx k
  rw [abs_le] at hxk
  constructor <;> linarith [hxk, hloEq, hhiEq]

private lemma payload_span_bounds {p : TangentPayload 6} {box : Box 6}
    (hp : p.check (grid := 4000) box = true) {x : Fin 6 → ℝ}
    (hx : InBox p x) {i r : ℕ} (hir : i + r ≤ 6) :
    (lowerSpan box i r : ℝ) / 4000 ≤ realSpan x i r ∧
      realSpan x i r ≤ ((upperSpan box i r : ℕ) + r : ℝ) / 4000 := by
  constructor
  · unfold lowerSpan realSpan
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun t ht => ?_
    rw [Finset.mem_Ico] at ht
    rw [show cellExt box.lo t = box.lo ⟨t, by omega⟩ by
      simp [cellExt, (show t < 6 by omega)]]
    rw [show Aggregation.gext x t = x ⟨t, by omega⟩ by
      simp [Aggregation.gext, (show t < 6 by omega)]]
    exact (payload_coordinate_bounds hp hx ⟨t, by omega⟩).1
  · unfold upperSpan realSpan
    calc
      ∑ t ∈ Finset.Ico i (i + r), Aggregation.gext x t
          ≤ ∑ t ∈ Finset.Ico i (i + r),
              ((cellExt box.hi t : ℕ) + 1 : ℝ) / 4000 := by
            refine Finset.sum_le_sum fun t ht => ?_
            rw [Finset.mem_Ico] at ht
            rw [show cellExt box.hi t = box.hi ⟨t, by omega⟩ by
              simp [cellExt, (show t < 6 by omega)]]
            rw [show Aggregation.gext x t = x ⟨t, by omega⟩ by
              simp [Aggregation.gext, (show t < 6 by omega)]]
            exact (payload_coordinate_bounds hp hx ⟨t, by omega⟩).2
      _ = ((∑ t ∈ Finset.Ico i (i + r), cellExt box.hi t : ℕ) + r : ℝ) /
          4000 := by
            rw [← Finset.sum_div]
            push_cast
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
            have : i + r - i = r := by omega
            rw [this]

/-- A checked wide range row is sound on the payload's entire closed real
box, including its upper faces. -/
theorem evidence_secondDerivative_sound_inBox
    (e : Evidence) (p : TangentPayload 6) (box : Box 6)
    (hp : p.check (grid := 4000) box = true)
    (he : e.check box = true) (x : Fin 6 → ℝ) (hx : InBox p x) :
    (e.range.lower : ℝ) ≤
      CurrentKernelTotalDerivatives.closedWeightD2Total
        (realSpan x e.geometry.start e.geometry.span) := by
  rw [Evidence.check, Bool.and_eq_true, Bool.and_eq_true] at he
  have hg := of_decide_eq_true he.2
  have hs := of_decide_eq_true (show e.geometry.check box = true from he.1.1)
  have hspan := payload_span_bounds hp hx hs.2.1
  have hmem : realSpan x e.geometry.start e.geometry.span ∈
      Icc ((e.range.left : ℝ) / 4000)
        ((e.range.right + 1 : ℕ) / 4000) := by
    rw [← hg.1, ← hg.2]
    constructor
    · have hcast : (e.geometry.left : ℝ) ≤
          lowerSpan box e.geometry.start e.geometry.span := by
        exact_mod_cast hs.2.2.2.1
      exact (div_le_div_of_nonneg_right hcast (by norm_num)).trans hspan.1
    · have hcast :
          ((upperSpan box e.geometry.start e.geometry.span : ℕ) +
            e.geometry.span : ℝ) ≤ ((e.geometry.right + 1 : ℕ) : ℝ) := by
        exact_mod_cast hs.2.2.2.2
      exact hspan.2.trans (div_le_div_of_nonneg_right hcast (by norm_num))
  exact e.range.sound he.1.2 hmem

private lemma rankOne_quadratic (t : HessianTerm 6) (d : Fin 6 → ℝ) :
    dotProduct d (castMatrix t.matrix *ᵥ d) =
      (t.coefficient : ℝ) *
        (∑ k, (t.direction k : ℝ) * d k) ^ 2 := by
  have hinner : ∀ i,
      (∑ j, ((t.coefficient * t.direction i * t.direction j : ℚ) : ℝ) * d j) =
        ((t.coefficient : ℝ) * t.direction i) *
          ∑ j, (t.direction j : ℝ) * d j := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  unfold dotProduct Matrix.mulVec castMatrix HessianTerm.matrix
  change (∑ i, d i *
      (∑ j, ((t.coefficient * t.direction i * t.direction j : ℚ) : ℝ) * d j)) = _
  simp_rw [hinner]
  calc
    (∑ i, d i * (((t.coefficient : ℝ) * t.direction i) *
        ∑ j, (t.direction j : ℝ) * d j)) =
      ∑ i, (d i * ((t.coefficient : ℝ) * t.direction i)) *
        ∑ j, (t.direction j : ℝ) * d j := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ =
      (∑ i, d i * ((t.coefficient : ℝ) * t.direction i)) *
        ∑ j, (t.direction j : ℝ) * d j := by rw [Finset.sum_mul]
    _ = (t.coefficient : ℝ) *
        (∑ k, (t.direction k : ℝ) * d k) ^ 2 := by
      have hfactor :
          (∑ i, d i * ((t.coefficient : ℝ) * t.direction i)) =
            (t.coefficient : ℝ) * ∑ i, (t.direction i : ℝ) * d i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hfactor]
      ring

private lemma direction_sum_eq_span (e : Evidence) (d : Fin 6 → ℝ)
    (hvalid : e.geometry.start + e.geometry.span ≤ 6) :
    (∑ k, (directionOfRange e k : ℝ) * d k) =
      realSpan d e.geometry.start e.geometry.span := by
  classical
  unfold directionOfRange realSpan
  have hcast : ∀ k : Fin 6,
      ((((if e.geometry.start ≤ k.val ∧
          k.val < e.geometry.start + e.geometry.span then 1 else 0) : ℚ)) : ℝ) =
        if e.geometry.start ≤ k.val ∧
          k.val < e.geometry.start + e.geometry.span then 1 else 0 := by
    intro k
    by_cases hk : e.geometry.start ≤ k.val ∧
        k.val < e.geometry.start + e.geometry.span <;> simp [hk]
  simp_rw [hcast]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun t ht => ⟨t, ?_⟩) ?_ ?_ ?_ ?_
  · rw [Finset.mem_Ico] at ht
    omega
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    simpa [Finset.mem_Ico] using ht
  · intro a ha b hb hab
    exact Fin.ext_iff.mp hab
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico] at hk
    exact ⟨k.val, by simpa [Finset.mem_Ico] using hk, Fin.ext rfl⟩
  · intro t ht
    have ht6 : t < 6 := by
      rw [Finset.mem_Ico] at ht
      omega
    simp [Aggregation.gext, ht6, Finset.mem_Ico]

/-- One checked production range row supplies exactly its weighted rank-one
quadratic lower bound at every point of the payload box. -/
theorem termOfRange_quadratic_le
    (e : Evidence) (p : TangentPayload 6) (box : Box 6)
    (hp : p.check (grid := 4000) box = true)
    (he : e.check box = true) (x d : Fin 6 → ℝ) (hx : InBox p x) :
    dotProduct d (castMatrix (HessianTerm.matrix (termOfRange e)) *ᵥ d) ≤
      Weighted.pairWeight e.geometry.start
          (e.geometry.start + e.geometry.span) *
        CurrentKernelTotalDerivatives.closedWeightD2Total
          (realSpan x e.geometry.start e.geometry.span) *
        (realSpan d e.geometry.start e.geometry.span) ^ 2 := by
  have he0 := he
  rw [Evidence.check, Bool.and_eq_true, Bool.and_eq_true] at he
  have hs := of_decide_eq_true
    (show e.geometry.check box = true from he.1.1)
  have hcurv := evidence_secondDerivative_sound_inBox e p box hp he0 x hx
  rw [rankOne_quadratic]
  change ((termOfRange e).coefficient : ℝ) *
      (∑ k, (directionOfRange e k : ℝ) * d k) ^ 2 ≤ _
  rw [direction_sum_eq_span e d hs.2.1]
  have hcoeff : ((termOfRange e).coefficient : ℝ) =
      Weighted.pairWeight e.geometry.start
        (e.geometry.start + e.geometry.span) * (e.range.lower : ℝ) := by
    simp [termOfRange, Weighted.pairWeight]
  rw [hcoeff]
  gcongr
  exact Weighted.pairWeight_nonneg _ _

end Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentHessian

end
