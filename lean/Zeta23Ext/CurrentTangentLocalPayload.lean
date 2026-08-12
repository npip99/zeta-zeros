/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentPayload
import Zeta23Ext.CurrentTangentRangeEvidence

/-!
# Leaf-local semantics for rational tangent payloads

The earlier generic payload theorem accepts global line-curvature semantics.
Production evidence is only valid on one leaf box.  This module gives the
correct interface: every analytic line and Hessian obligation is conditional
on the endpoint belonging to the payload's continuous midpoint/radius box.
It also proves explicitly that the whole center-to-endpoint segment remains
inside that box.
-/

noncomputable section

open Set Matrix
open scoped BigOperators

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.Local

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentTangent

/-- Continuous closed box described by the exact payload midpoint and radius. -/
def InBox {q : ℕ} (p : TangentPayload q) (x : Fin q → ℝ) : Prop :=
  ∀ i, |x i - (p.center i : ℝ)| ≤ (p.radius i : ℝ)

/-- Every center-to-box-point segment stays in the same continuous box. -/
theorem segment_inBox {q : ℕ} {p : TangentPayload q} {x : Fin q → ℝ}
    (hx : InBox p x) {t : ℝ} (ht : t ∈ Icc 0 1) :
    InBox p (fun i => (p.center i : ℝ) +
      t * (x i - (p.center i : ℝ))) := by
  intro i
  rw [show (p.center i : ℝ) + t * (x i - (p.center i : ℝ)) - p.center i =
      t * (x i - (p.center i : ℝ)) by ring, abs_mul]
  calc
    |t| * |x i - (p.center i : ℝ)| = t * |x i - (p.center i : ℝ)| := by
      rw [abs_of_nonneg ht.1]
    _ ≤ 1 * |x i - (p.center i : ℝ)| := by
      exact mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)
    _ ≤ (p.radius i : ℝ) := by simpa using hx i

/-- Analytic meaning of one payload, scoped to its certified leaf.  In a
production instantiation, `lineSecond_lower` is assembled from wide
`Range.Evidence.secondDerivative_sound` rows for all 21 pair spans. -/
structure Semantics {q : ℕ} (p : TangentPayload q) where
  objective : (Fin q → ℝ) → ℝ
  gradient : (Fin q → ℝ) → Fin q → ℝ
  lineFirst : (Fin q → ℝ) → ℝ → ℝ
  lineSecond : (Fin q → ℝ) → ℝ → ℝ
  value_mem : (p.value.lower : ℝ) ≤ objective (fun i => p.center i)
  gradient_mem : ∀ i,
    ((p.gradient i).lower : ℝ) ≤ gradient (fun j => p.center j) i ∧
      gradient (fun j => p.center j) i ≤ (p.gradient i).upper
  continuous_line : ∀ (x : Fin q → ℝ), InBox p x → ContinuousOn
    (fun t => objective (fun i => (p.center i : ℝ) +
      t * (x i - (p.center i : ℝ)))) (Icc 0 1)
  hasLineFirst : ∀ (x : Fin q → ℝ), InBox p x → ∀ t,
    t ∈ interior (Icc (0 : ℝ) 1) →
    HasDerivWithinAt
      (fun u => objective (fun i => (p.center i : ℝ) +
        u * (x i - (p.center i : ℝ))))
      (lineFirst x t) (interior (Icc 0 1)) t
  hasLineSecond : ∀ (x : Fin q → ℝ), InBox p x → ∀ t,
    t ∈ interior (Icc (0 : ℝ) 1) →
    HasDerivWithinAt (lineFirst x) (lineSecond x t) (interior (Icc 0 1)) t
  /-- The segment premise is explicit, so a range certificate for one leaf
  cannot be silently promoted to a global Hessian assertion. -/
  lineSecond_lower : ∀ (x : Fin q → ℝ), InBox p x → ∀ t,
    t ∈ interior (Icc (0 : ℝ) 1) →
    InBox p (fun i => (p.center i : ℝ) +
      t * (x i - (p.center i : ℝ))) →
    dotProduct (fun i => x i - (p.center i : ℝ))
        (castMatrix (hessianMatrix p.hessianTerms) *ᵥ
          (fun i => x i - (p.center i : ℝ))) ≤ lineSecond x t
  hasLineDerivZero : ∀ x : Fin q → ℝ, InBox p x → HasDerivAt
    (fun t => objective (fun i => (p.center i : ℝ) +
      t * (x i - (p.center i : ℝ))))
    (∑ i, gradient (fun j => p.center j) i *
      (x i - (p.center i : ℝ))) 0

private lemma check_facts {q grid : ℕ} {p : TangentPayload q} {box : Box q}
    (h : p.check (grid := grid) box = true) :
    (0 < grid ∧
      (∀ i, p.center i = (box.lo i + box.hi i + 1 : ℚ) / (2 * grid)) ∧
      (∀ i, p.radius i = (box.hi i - box.lo i + 1 : ℚ) / (2 * grid)) ∧
      (∀ i, 0 ≤ p.radius i) ∧
      p.value.lower ≤ p.value.upper ∧
      (∀ i, (p.gradient i).lower ≤ (p.gradient i).upper) ∧
      p.target ≤ p.affineLower) ∧
    p.ldl.check (hessianMatrix p.hessianTerms) = true := by
  rw [TangentPayload.check, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, h.2⟩

private lemma abs_le_absUpper {I : QInterval} {x : ℝ}
    (h : (I.lower : ℝ) ≤ x ∧ x ≤ I.upper) :
    |x| ≤ (I.absUpper : ℝ) := by
  simp only [QInterval.absUpper, Rat.cast_max, Rat.cast_abs]
  rw [abs_le]
  constructor
  · calc
      -max |(I.lower : ℝ)| |(I.upper : ℝ)| ≤ -|(I.lower : ℝ)| :=
        neg_le_neg (le_max_left _ _)
      _ ≤ (I.lower : ℝ) := neg_abs_le _
      _ ≤ x := h.1
  · exact h.2.trans ((le_abs_self (I.upper : ℝ)).trans (le_max_right _ _))

private theorem point_inBox {q grid : ℕ} {p : TangentPayload q}
    {box : Box q} (hcheck : p.check (grid := grid) box = true)
    (point : {x : Fin q → ℝ // ∀ i, 0 ≤ x i})
    (hbox : box.Contains (locateOnGrid grid point)) : InBox p point.1 := by
  intro i
  have hf := (check_facts hcheck).1
  have hcell := locateOnGrid_cell hf.1 point i
  have hloNat := (hbox i).1
  have hhiNat := (hbox i).2
  have hlo : (box.lo i : ℝ) / grid ≤ point.1 i := by
    exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hloNat)
      (by positivity)) hcell.1
  have hhi : point.1 i ≤ ((box.hi i : ℕ) + 1 : ℝ) / grid := by
    exact hcell.2.le.trans (div_le_div_of_nonneg_right
      (by exact_mod_cast Nat.add_le_add_right hhiNat 1) (by positivity))
  rw [abs_le]
  have hc := congrArg (fun z : ℚ => (z : ℝ)) (hf.2.1 i)
  have hr := congrArg (fun z : ℚ => (z : ℝ)) (hf.2.2.1 i)
  push_cast at hc hr
  have hgridR : (grid : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hf.1)
  have hloEq : (p.center i : ℝ) - p.radius i = (box.lo i : ℝ) / grid := by
    rw [hc, hr]
    field_simp
    ring
  have hhiEq : (p.center i : ℝ) + p.radius i =
      ((box.hi i : ℕ) + 1 : ℝ) / grid := by
    rw [hc, hr]
    field_simp
    ring
  constructor <;> linarith [hlo, hhi, hloEq, hhiEq]

/-- Leaf-local soundness of a rational tangent payload. -/
theorem sound {q grid : ℕ} (p : TangentPayload q) (sem : Semantics p)
    (box : Box q) (hcheck : p.check (grid := grid) box = true)
    (point : {x : Fin q → ℝ // ∀ i, 0 ≤ x i})
    (hbox : box.Contains (locateOnGrid grid point)) :
    (p.target : ℝ) ≤ sem.objective point.1 := by
  have hf := check_facts hcheck
  have hpoint := point_inBox hcheck point hbox
  have hpsd := p.ldl.check_sound (hessianMatrix p.hessianTerms) hf.2
  have hquad : 0 ≤
      dotProduct (fun i => point.1 i - (p.center i : ℝ))
        (castMatrix (hessianMatrix p.hessianTerms) *ᵥ
          (fun i => point.1 i - (p.center i : ℝ))) := by
    simpa using hpsd.dotProduct_mulVec_nonneg
      (fun i => point.1 i - (p.center i : ℝ))
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun t => sem.objective (fun i => (p.center i : ℝ) +
        t * (point.1 i - (p.center i : ℝ)))) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (sem.continuous_line point.1 hpoint) (sem.hasLineFirst point.1 hpoint)
      (sem.hasLineSecond point.1 hpoint)
    intro t ht
    exact hquad.trans (sem.lineSecond_lower point.1 hpoint t ht
      (segment_inBox hpoint (interior_subset ht)))
  have hslope := hconv.le_slope_of_hasDerivAt
    (x := (0 : ℝ)) (y := 1) (by norm_num) (by norm_num) zero_lt_one
      (sem.hasLineDerivZero point.1 hpoint)
  have hsupport :
      sem.objective (fun i => (p.center i : ℝ)) +
          ∑ i, sem.gradient (fun j => p.center j) i *
            (point.1 i - (p.center i : ℝ)) ≤ sem.objective point.1 := by
    simpa [slope, sub_eq_add_neg, add_comm] using hslope
  have hgradient :
      -(∑ i, ((p.gradient i).absUpper : ℝ) * (p.radius i : ℝ)) ≤
        ∑ i, sem.gradient (fun j => p.center j) i *
          (point.1 i - (p.center i : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hg := abs_le_absUpper (sem.gradient_mem i)
    have hx := hpoint i
    have hga : (0 : ℝ) ≤ (p.gradient i).absUpper := by
      simp [QInterval.absUpper]
    calc
      -(((p.gradient i).absUpper : ℝ) * (p.radius i : ℝ))
          ≤ -(|sem.gradient (fun j => p.center j) i| *
            |point.1 i - (p.center i : ℝ)|) := by gcongr
      _ = -|sem.gradient (fun j => p.center j) i *
            (point.1 i - (p.center i : ℝ))| := by rw [abs_mul]
      _ ≤ sem.gradient (fun j => p.center j) i *
            (point.1 i - (p.center i : ℝ)) := neg_abs_le _
  have haffine : (p.target : ℝ) ≤ (p.value.lower : ℝ) -
      ∑ i, ((p.gradient i).absUpper : ℝ) * (p.radius i : ℝ) := by
    exact_mod_cast hf.1.2.2.2.2.2.2
  calc
    (p.target : ℝ) ≤ (p.value.lower : ℝ) -
        ∑ i, ((p.gradient i).absUpper : ℝ) * (p.radius i : ℝ) := haffine
    _ ≤ sem.objective (fun i => (p.center i : ℝ)) +
        ∑ i, sem.gradient (fun j => p.center j) i *
          (point.1 i - (p.center i : ℝ)) := by linarith [sem.value_mem, hgradient]
    _ ≤ sem.objective point.1 := hsupport

def tangentOK {q grid : ℕ} (p : TangentPayload q) (box : Box q) : Bool :=
  p.check (grid := grid) box

theorem tangentOK_sound {q grid : ℕ}
    (semantics : ∀ p : TangentPayload q, Semantics p)
    (p : TangentPayload q) (box : Box q)
    (hcheck : tangentOK (grid := grid) p box = true) :
    ∀ point : {x : Fin q → ℝ // ∀ i, 0 ≤ x i},
      box.Contains (locateOnGrid grid point) →
        (p.target : ℝ) ≤ (semantics p).objective point.1 := by
  intro point hbox
  exact sound p (semantics p) box hcheck point hbox

/-! ## Six-gap production package -/

/-- Exact rank-one direction for the consecutive span carried by a range
evidence row. -/
def directionOfRange
    (e : CurrentTangent.Range.Evidence) (i : Fin 6) : ℚ :=
  if e.geometry.start ≤ i.val ∧
      i.val < e.geometry.start + e.geometry.span then 1 else 0

/-- The Hessian coefficient is the exact nonnegative pair weight times the
certified common lower bound for `w''` over the full span range. -/
def termOfRange (e : CurrentTangent.Range.Evidence) : HessianTerm 6 where
  coefficient :=
    (Weighted.pairWeightNumerator e.geometry.start
      (e.geometry.start + e.geometry.span) : ℚ) / 1000000 * e.range.lower
  direction := directionOfRange e

/-- Production tangent object.  The checked range rows are not auxiliary
metadata: `check` requires the payload Hessian list to equal their exact
pair-weighted rank-one images. -/
structure Certificate where
  payload : TangentPayload 6
  ranges : List CurrentTangent.Range.Evidence

/-- Canonical ordered support of the exact pair-weight table.  Pair `(1,5)`
is intentionally absent because its exact weight is zero; every other pair
appears once as `(start, span)`. -/
def canonicalRangeKeys : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
   (1, 1), (1, 2), (1, 3), (1, 5),
   (2, 1), (2, 2), (2, 3), (2, 4),
   (3, 1), (3, 2), (3, 3),
   (4, 1), (4, 2),
   (5, 1)]

def Certificate.rangeKeys (c : Certificate) : List (ℕ × ℕ) :=
  c.ranges.map fun e => (e.geometry.start, e.geometry.span)

noncomputable def Certificate.check (c : Certificate) (box : Box 6) : Bool :=
  c.payload.check (grid := 4000) box &&
    c.ranges.all (fun e => e.check box) &&
    decide (c.rangeKeys = canonicalRangeKeys ∧
      c.payload.hessianTerms = c.ranges.map termOfRange ∧
      c.payload.target = 509 / 100000)

private lemma certificate_check_facts {c : Certificate} {box : Box 6}
    (h : c.check box = true) :
    c.payload.check (grid := 4000) box = true ∧
      (∀ e ∈ c.ranges, e.check box = true) ∧
      c.rangeKeys = canonicalRangeKeys ∧
      c.payload.hessianTerms = c.ranges.map termOfRange ∧
      c.payload.target = 509 / 100000 := by
  rw [Certificate.check, Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨h.1.1, ?_, of_decide_eq_true h.2⟩
  exact List.all_eq_true.mp h.1.2

/-- Public finite-interface theorem: acceptance forces exactly the canonical
20 nonzero pair spans, hence no omitted or duplicated Hessian pair. -/
theorem Certificate.check_support {c : Certificate} {box : Box 6}
    (h : c.check box = true) : c.rangeKeys = canonicalRangeKeys :=
  (certificate_check_facts h).2.2.1

theorem Certificate.check_terms {c : Certificate} {box : Box 6}
    (h : c.check box = true) :
    c.payload.hessianTerms = c.ranges.map termOfRange :=
  (certificate_check_facts h).2.2.2.1

theorem Certificate.check_target {c : Certificate} {box : Box 6}
    (h : c.check box = true) : c.payload.target = 509 / 100000 :=
  (certificate_check_facts h).2.2.2.2

/-- Every range row accepted as part of a production payload provides its
true current-kernel curvature bound over the corresponding leaf span. -/
theorem Certificate.range_sound {c : Certificate} {box : Box 6}
    (hcheck : c.check box = true) {e : CurrentTangent.Range.Evidence}
    (he : e ∈ c.ranges) (gaps : CurrentGapVector)
    (hbox : box.Contains (CurrentReplay.locateGaps 4000 gaps)) :
    (e.range.lower : ℝ) ≤ CurrentKernelDerivatives.closedWeightD2
      (CurrentReplay.realSpan gaps.1 e.geometry.start e.geometry.span) := by
  exact e.secondDerivative_sound box
    ((certificate_check_facts hcheck).2.1 e he) gaps hbox

/-- Soundness after the analytic producer has assembled the checked range
rows into the leaf-local `Semantics.lineSecond_lower` theorem. -/
theorem Certificate.sound (c : Certificate) (sem : Semantics c.payload)
    (box : Box 6) (hcheck : c.check box = true)
    (point : CurrentGapVector)
    (hbox : box.Contains (CurrentReplay.locateGaps 4000 point)) :
    (c.payload.target : ℝ) ≤ sem.objective point.1 := by
  exact Zeta23Ext.VerifiedCertificate.CurrentTangent.Local.sound
    c.payload sem box (certificate_check_facts hcheck).1 point hbox

/-- The analytic producer's current-specific seam.  Constructing this object
requires the total derivative theorems for `CurrentWindow.weight` and exact
assembly of all 20 checked nonzero pair rows; no arbitrary objective can be
substituted once this interface is used. -/
structure CurrentSemantics (c : Certificate) where
  toLocal : Semantics c.payload
  objective_eq : ∀ gaps : Fin 6 → ℝ,
    toLocal.objective gaps = Weighted.F6 CurrentWindow.weight gaps

/-- A checked current-specific tangent certificate proves the exact local
inequality used downstream.  Its target equality and complete 20-pair
support are Boolean obligations of `Certificate.check`. -/
theorem Certificate.current_sound (c : Certificate) (sem : CurrentSemantics c)
    (box : Box 6) (hcheck : c.check box = true)
    (point : CurrentGapVector)
    (hbox : box.Contains (CurrentReplay.locateGaps 4000 point)) :
    Weighted.beta ≤ Weighted.F6 CurrentWindow.weight point.1 := by
  have h := c.sound sem.toLocal box hcheck point hbox
  have ht := (certificate_check_facts hcheck).2.2.2.2
  rw [sem.objective_eq] at h
  have htR : (c.payload.target : ℝ) = Weighted.beta := by
    rw [ht]
    norm_num [Weighted.beta]
  rw [← htR]
  exact h

/-- Annotated-forest predicate for the fully linked production payload. -/
def certificateTangentOK (c : Certificate) (box : Box 6) : Bool := c.check box

theorem certificateTangentOK_sound
    (semantics : ∀ c : Certificate, CurrentSemantics c)
    (c : Certificate) (box : Box 6)
    (hcheck : certificateTangentOK c box = true) :
    ∀ point : CurrentGapVector,
      box.Contains (CurrentReplay.locateGaps 4000 point) →
        Weighted.beta ≤ Weighted.F6 CurrentWindow.weight point.1 := by
  intro point hbox
  exact c.current_sound (semantics c) box hcheck point hbox

end Zeta23Ext.VerifiedCertificate.CurrentTangent.Local

end
