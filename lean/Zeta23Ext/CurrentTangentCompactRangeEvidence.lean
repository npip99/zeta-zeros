/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentCurvatureRMQ
import Zeta23Ext.CurrentTangentCurrentSemantics

/-!
# Compact production tangent curvature evidence

This is the leaf-facing companion to the globally checked sparse table.
Unlike the legacy range format, it never stores or enumerates semantic cells
inside a leaf.  Each of the canonical twenty rows contains only geometry, a
common rational lower bound, and two sparse-block references.
-/

noncomputable section

open Set

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactRange

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay
open Zeta23Ext.VerifiedCertificate.CurrentTangent
open Zeta23Ext.VerifiedCertificate.CurrentTangent.Local
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentSemantics
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CurvatureRMQ

/-- Consecutive-gap geometry paired with one constant-size RMQ query. -/
structure Evidence where
  start : ℕ
  span : ℕ
  query : RangeWitness
  deriving DecidableEq

noncomputable def Evidence.check (table : SparseTable) (e : Evidence)
    (box : Box 6) : Bool := by
  classical
  exact e.query.check table && decide
    (0 < e.span ∧ e.start + e.span ≤ 6 ∧
      table.cells.first + e.query.left ≤ lowerSpan box e.start e.span ∧
      upperSpan box e.start e.span + e.span ≤
        table.cells.first + e.query.right + 1)

private lemma evidence_check_facts {table : SparseTable} {e : Evidence}
    {box : Box 6} (h : e.check table box = true) :
    e.query.check table = true ∧ 0 < e.span ∧ e.start + e.span ≤ 6 ∧
      table.cells.first + e.query.left ≤ lowerSpan box e.start e.span ∧
      upperSpan box e.start e.span + e.span ≤
        table.cells.first + e.query.right + 1 := by
  rw [Evidence.check, Bool.and_eq_true] at h
  exact ⟨h.1, of_decide_eq_true h.2⟩

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

/-- Compact row soundness on the entire closed payload box. -/
theorem Evidence.secondDerivative_sound_inBox (table : SparseTable)
    (htable : table.check = true) (e : Evidence) (p : TangentPayload 6)
    (box : Box 6) (hp : p.check (grid := 4000) box = true)
    (he : e.check table box = true) (x : Fin 6 → ℝ) (hx : InBox p x) :
    (e.query.lower : ℝ) ≤
      CurrentKernelTotalDerivatives.closedWeightD2Total
        (realSpan x e.start e.span) := by
  have hf := evidence_check_facts he
  have hs := payload_span_bounds hp hx hf.2.2.1
  apply e.query.sound table htable hf.1
  constructor
  · have hcast : ((table.cells.first + e.query.left : ℕ) : ℝ) ≤
        lowerSpan box e.start e.span := by exact_mod_cast hf.2.2.2.1
    exact (div_le_div_of_nonneg_right hcast (by norm_num)).trans hs.1
  · have hcast : ((upperSpan box e.start e.span : ℕ) + e.span : ℝ) ≤
        (table.cells.first + e.query.right + 1 : ℕ) := by
      exact_mod_cast hf.2.2.2.2
    exact hs.2.trans (div_le_div_of_nonneg_right hcast (by norm_num))

/-- Exact rank-one term consumed by the compact Hessian assembly. -/
def termOfEvidence (e : Evidence) : HessianTerm 6 where
  coefficient :=
    (Weighted.pairWeightNumerator e.start (e.start + e.span) : ℚ) /
      1000000 * e.query.lower
  direction i := if e.start ≤ i.val ∧ i.val < e.start + e.span then 1 else 0

/-- Leaf data contains exactly twenty compact rows, not their semantic cells. -/
structure Certificate where
  payload : TangentPayload 6
  ranges : List Evidence

def Certificate.rangeKeys (c : Certificate) : List (ℕ × ℕ) :=
  c.ranges.map fun e => (e.start, e.span)

noncomputable def Certificate.check (table : SparseTable) (c : Certificate)
    (box : Box 6) : Bool := by
  classical
  exact c.payload.check (grid := 4000) box &&
    c.ranges.all (fun e => e.check table box) &&
    decide (c.rangeKeys = Local.canonicalRangeKeys ∧
      c.payload.hessianTerms = c.ranges.map termOfEvidence ∧
      c.payload.target = 509 / 100000)

private lemma certificate_check_facts {table : SparseTable} {c : Certificate}
    {box : Box 6} (h : c.check table box = true) :
    c.payload.check (grid := 4000) box = true ∧
      (∀ e ∈ c.ranges, e.check table box = true) ∧
      c.rangeKeys = Local.canonicalRangeKeys ∧
      c.payload.hessianTerms = c.ranges.map termOfEvidence ∧
      c.payload.target = 509 / 100000 := by
  rw [Certificate.check, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, List.all_eq_true.mp h.1.2, of_decide_eq_true h.2⟩

theorem Certificate.check_support {table : SparseTable} {c : Certificate}
    {box : Box 6} (h : c.check table box = true) :
    c.rangeKeys = Local.canonicalRangeKeys := (certificate_check_facts h).2.2.1

theorem Certificate.check_terms {table : SparseTable} {c : Certificate}
    {box : Box 6} (h : c.check table box = true) :
    c.payload.hessianTerms = c.ranges.map termOfEvidence :=
  (certificate_check_facts h).2.2.2.1

theorem Certificate.check_target {table : SparseTable} {c : Certificate}
    {box : Box 6} (h : c.check table box = true) :
    c.payload.target = 509 / 100000 := (certificate_check_facts h).2.2.2.2

theorem Certificate.range_sound {table : SparseTable} (htable : table.check = true)
    {c : Certificate} {box : Box 6} (hcheck : c.check table box = true)
    {e : Evidence} (he : e ∈ c.ranges) (x : Fin 6 → ℝ)
    (hx : InBox c.payload x) :
    (e.query.lower : ℝ) ≤
      CurrentKernelTotalDerivatives.closedWeightD2Total
        (realSpan x e.start e.span) := by
  exact e.secondDerivative_sound_inBox table htable c.payload box
    (certificate_check_facts hcheck).1
    ((certificate_check_facts hcheck).2.1 e he) x hx

end Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactRange

end
