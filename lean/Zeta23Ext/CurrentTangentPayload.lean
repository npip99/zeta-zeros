/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentEvidence
import Mathlib.Analysis.Convex.Deriv
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Exact-rational payloads for convex tangent leaves

This is the generated-data layer above `CurrentTangentEvidence`.  It checks:

* exact box midpoint and radius data;
* signed value and gradient enclosures;
* a rational sum of signed rank-one Hessian lower terms;
* an exact rational `L D Lᵀ` factorization with nonnegative pivots; and
* the final affine tangent lower bound.

The semantic structure at the end lists the remaining analytic producer
inputs explicitly: value/gradient enclosure theorems and first/second line
derivative theorems connecting the rank-one Hessian data to the real
objective.  Thus accepting generated data never amounts to trusting its Arb
decimal strings.
-/

noncomputable section

open Set Matrix
open scoped BigOperators

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate

abbrev QMatrix (q : ℕ) := Matrix (Fin q) (Fin q) ℚ

def castMatrix {q : ℕ} (M : QMatrix q) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => (M i j : ℝ)

/-- A signed rational rank-one lower term `coefficient * v vᵀ`. -/
structure HessianTerm (q : ℕ) where
  coefficient : ℚ
  direction : Fin q → ℚ
  deriving DecidableEq

def HessianTerm.matrix {q : ℕ} (t : HessianTerm q) : QMatrix q :=
  fun i j => t.coefficient * t.direction i * t.direction j

def hessianMatrix {q : ℕ} (terms : List (HessianTerm q)) : QMatrix q :=
  fun i j => (terms.map fun t => t.matrix i j).sum

/-- Exact `L D Lᵀ` data.  The Boolean checker also enforces the conventional
unit lower-triangular shape, although positivity only needs the factorization
and nonnegative diagonal. -/
structure LDLCertificate (q : ℕ) where
  lower : QMatrix q
  diagonal : Fin q → ℚ

def LDLCertificate.reconstruct {q : ℕ} (c : LDLCertificate q) : QMatrix q :=
  fun i j => ∑ k, c.lower i k * c.diagonal k * c.lower j k

noncomputable def LDLCertificate.check {q : ℕ} (c : LDLCertificate q)
    (M : QMatrix q) : Bool := by
  classical
  exact decide ((∀ i j, M i j = c.reconstruct i j) ∧
    (∀ i, 0 ≤ c.diagonal i) ∧
    (∀ i, c.lower i i = 1) ∧
    (∀ i j, i < j → c.lower i j = 0))

private lemma ldl_check_facts {q : ℕ} {c : LDLCertificate q} {M : QMatrix q}
    (h : c.check M = true) :
    (∀ i j, M i j = c.reconstruct i j) ∧
      (∀ i, 0 ≤ c.diagonal i) ∧
      (∀ i, c.lower i i = 1) ∧
      (∀ i j, i < j → c.lower i j = 0) := by
  classical
  simpa [LDLCertificate.check] using of_decide_eq_true h

private lemma cast_reconstruct {q : ℕ} (c : LDLCertificate q) :
    castMatrix c.reconstruct =
      castMatrix c.lower * diagonal (fun k => (c.diagonal k : ℝ)) *
        (castMatrix c.lower)ᵀ := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp [castMatrix, LDLCertificate.reconstruct, Matrix.mul_diagonal]

private theorem reconstruct_posSemidef {q : ℕ} (c : LDLCertificate q)
    (hD : ∀ k, 0 ≤ c.diagonal k) : (castMatrix c.reconstruct).PosSemidef := by
  classical
  rw [cast_reconstruct]
  have hd : ∀ i, (0 : ℝ) ≤ c.diagonal i := fun i => by
    exact_mod_cast hD i
  have hdiag : (Matrix.diagonal (fun i => (c.diagonal i : ℝ))).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · exact Matrix.isHermitian_diagonal _
    · intro x
      unfold dotProduct
      apply Finset.sum_nonneg
      intro i _
      rw [Matrix.mulVec_diagonal]
      simp only [star_trivial]
      nlinarith [hd i, sq_nonneg (x i)]
  exact hdiag.mul_mul_conjTranspose_same (castMatrix c.lower)

/-- Kernel-checked LDL acceptance proves positive semidefiniteness of the
cast rational Hessian lower matrix. -/
theorem LDLCertificate.check_sound {q : ℕ} (c : LDLCertificate q)
    (M : QMatrix q) (h : c.check M = true) : (castMatrix M).PosSemidef := by
  have hf := ldl_check_facts h
  have hM : castMatrix M = castMatrix c.reconstruct := by
    ext i j
    simp only [castMatrix]
    exact_mod_cast hf.1 i j
  rw [hM]
  exact reconstruct_posSemidef c hf.2.1

/-- Rational interval used for signed value and gradient enclosures. -/
structure QInterval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq

def QInterval.absUpper (I : QInterval) : ℚ := max |I.lower| |I.upper|

/-- Complete finite payload of one convex tangent leaf. -/
structure TangentPayload (q : ℕ) where
  center : Fin q → ℚ
  radius : Fin q → ℚ
  value : QInterval
  gradient : Fin q → QInterval
  hessianTerms : List (HessianTerm q)
  ldl : LDLCertificate q
  target : ℚ

def TangentPayload.affineLower {q : ℕ} (p : TangentPayload q) : ℚ :=
  p.value.lower - ∑ i, (p.gradient i).absUpper * p.radius i

/-- Executable payload checker.  Midpoints/radii follow the verifier's closed
cell convention `[lo/grid,(hi+1)/grid]`. -/
noncomputable def TangentPayload.check {q grid : ℕ} (p : TangentPayload q)
    (box : Box q) : Bool := by
  classical
  exact decide (0 < grid ∧
    (∀ i, p.center i = (box.lo i + box.hi i + 1 : ℚ) / (2 * grid)) ∧
    (∀ i, p.radius i = (box.hi i - box.lo i + 1 : ℚ) / (2 * grid)) ∧
    (∀ i, 0 ≤ p.radius i) ∧
    p.value.lower ≤ p.value.upper ∧
    (∀ i, (p.gradient i).lower ≤ (p.gradient i).upper) ∧
    p.target ≤ p.affineLower) &&
      p.ldl.check (hessianMatrix p.hessianTerms)

private lemma payload_check_facts {q grid : ℕ} {p : TangentPayload q} {box : Box q}
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

private lemma abs_le_interval_absUpper {I : QInterval} {x : ℝ}
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

/-- Analytic meaning of one generated payload.  These are precisely the
non-finite producer obligations.  In production, `lineSecond_lower` is built
from the 21 `SpanEvidence.secondDerivative_sound` theorems and the exact pair
weights. -/
structure TangentPayload.Semantics {q : ℕ} (p : TangentPayload q) where
  objective : (Fin q → ℝ) → ℝ
  gradient : (Fin q → ℝ) → Fin q → ℝ
  lineFirst : (Fin q → ℝ) → ℝ → ℝ
  lineSecond : (Fin q → ℝ) → ℝ → ℝ
  value_mem : (p.value.lower : ℝ) ≤ objective (fun i => p.center i)
  gradient_mem : ∀ i,
    ((p.gradient i).lower : ℝ) ≤ gradient (fun j => p.center j) i ∧
      gradient (fun j => p.center j) i ≤ (p.gradient i).upper
  continuous_line : ∀ x : Fin q → ℝ, ContinuousOn
    (fun t => objective (fun i => (p.center i : ℝ) +
      t * (x i - (p.center i : ℝ)))) (Icc 0 1)
  hasLineFirst : ∀ (x : Fin q → ℝ) t, t ∈ interior (Icc (0 : ℝ) 1) →
    HasDerivWithinAt
      (fun u => objective (fun i => (p.center i : ℝ) +
        u * (x i - (p.center i : ℝ))))
      (lineFirst x t) (interior (Icc 0 1)) t
  hasLineSecond : ∀ (x : Fin q → ℝ) t, t ∈ interior (Icc (0 : ℝ) 1) →
    HasDerivWithinAt (lineFirst x) (lineSecond x t) (interior (Icc 0 1)) t
  lineSecond_lower : ∀ (x : Fin q → ℝ) t, t ∈ interior (Icc (0 : ℝ) 1) →
    dotProduct (fun i => x i - (p.center i : ℝ))
        (castMatrix (hessianMatrix p.hessianTerms) *ᵥ
          (fun i => x i - (p.center i : ℝ))) ≤ lineSecond x t
  hasLineDerivZero : ∀ x : Fin q → ℝ, HasDerivAt
    (fun t => objective (fun i => (p.center i : ℝ) +
      t * (x i - (p.center i : ℝ))))
    (∑ i, gradient (fun j => p.center j) i *
      (x i - (p.center i : ℝ))) 0

private theorem coordinate_mem_radius {q grid : ℕ} {p : TangentPayload q}
    {box : Box q} (hcheck : p.check (grid := grid) box = true)
    (point : {x : Fin q → ℝ // ∀ i, 0 ≤ x i})
    (hbox : box.Contains (locateOnGrid grid point)) (i : Fin q) :
    |point.1 i - (p.center i : ℝ)| ≤ (p.radius i : ℝ) := by
  have hf := (payload_check_facts hcheck).1
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

/-- Soundness of the whole rational tangent payload.  LDL positivity supplies
convexity along the center-to-point segment; the signed gradient intervals
then bound the supporting affine plane over the entire box. -/
theorem TangentPayload.sound {q grid : ℕ} (p : TangentPayload q)
    (sem : p.Semantics) (box : Box q) (hcheck : p.check (grid := grid) box = true)
    (point : {x : Fin q → ℝ // ∀ i, 0 ≤ x i})
    (hbox : box.Contains (locateOnGrid grid point)) :
    (p.target : ℝ) ≤ sem.objective point.1 := by
  have hf := payload_check_facts hcheck
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
      (sem.continuous_line point.1) (sem.hasLineFirst point.1)
      (sem.hasLineSecond point.1)
    intro t ht
    exact hquad.trans (sem.lineSecond_lower point.1 t ht)
  have hslope := hconv.le_slope_of_hasDerivAt
    (x := (0 : ℝ)) (y := 1) (by norm_num) (by norm_num) zero_lt_one
      (sem.hasLineDerivZero point.1)
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
    have hg := abs_le_interval_absUpper (sem.gradient_mem i)
    have hx := coordinate_mem_radius hcheck point hbox i
    have hga : (0 : ℝ) ≤ (p.gradient i).absUpper := by
      simp [QInterval.absUpper]
    calc
      -(((p.gradient i).absUpper : ℝ) * (p.radius i : ℝ))
          ≤ -(|sem.gradient (fun j => p.center j) i| *
            |point.1 i - (p.center i : ℝ)|) := by
              gcongr
      _ = -|sem.gradient (fun j => p.center j) i *
            (point.1 i - (p.center i : ℝ))| := by rw [abs_mul]
      _ ≤ sem.gradient (fun j => p.center j) i *
            (point.1 i - (p.center i : ℝ)) := neg_abs_le _
  have haffine : (p.target : ℝ) ≤
      (p.value.lower : ℝ) -
        ∑ i, ((p.gradient i).absUpper : ℝ) * (p.radius i : ℝ) := by
    have := hf.1.2.2.2.2.2.2
    exact_mod_cast this
  calc
    (p.target : ℝ) ≤ (p.value.lower : ℝ) -
        ∑ i, ((p.gradient i).absUpper : ℝ) * (p.radius i : ℝ) := haffine
    _ ≤ sem.objective (fun i => (p.center i : ℝ)) +
        ∑ i, sem.gradient (fun j => p.center j) i *
          (point.1 i - (p.center i : ℝ)) := by linarith [sem.value_mem, hgradient]
    _ ≤ sem.objective point.1 := hsupport

/-- Direct annotated-forest adapter.  A generated evidence family supplies
one semantic theorem package per payload; the checker itself remains pure
Boolean exact arithmetic. -/
def payloadTangentOK {q grid : ℕ} (p : TangentPayload q) (box : Box q) : Bool :=
  p.check (grid := grid) box

theorem payloadTangentOK_sound {q grid : ℕ}
    (semantics : ∀ p : TangentPayload q, p.Semantics)
    (p : TangentPayload q) (box : Box q)
    (hcheck : payloadTangentOK (grid := grid) p box = true) :
    ∀ point : {x : Fin q → ℝ // ∀ i, 0 ≤ x i},
      box.Contains (locateOnGrid grid point) →
        (p.target : ℝ) ≤ (semantics p).objective point.1 := by
  intro point hbox
  exact p.sound (semantics p) box hcheck point hbox

end Zeta23Ext.VerifiedCertificate.CurrentTangent

end
