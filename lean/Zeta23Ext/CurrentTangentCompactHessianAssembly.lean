/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentCompactRangeEvidence
import Zeta23Ext.CurrentTangentCurrentAssembly

/-!
# Compact current-tangent Hessian assembly

This is the production-scale parallel to the legacy Hessian assembly.  It
uses twenty constant-size RMQ queries and never reconstructs a per-leaf list
of semantic curvature cells.
-/

noncomputable section

open Set Matrix
open scoped BigOperators

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactHessian

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay
open Zeta23Ext.VerifiedCertificate.CurrentTangent
open Zeta23Ext.VerifiedCertificate.CurrentTangent.Local
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentSemantics
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CurvatureRMQ
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactRange

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
    _ = (∑ i, d i * ((t.coefficient : ℝ) * t.direction i)) *
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
    (hvalid : e.start + e.span ≤ 6) :
    (∑ k, ((termOfEvidence e).direction k : ℝ) * d k) =
      realSpan d e.start e.span := by
  classical
  unfold termOfEvidence realSpan
  have hcast : ∀ k : Fin 6,
      ((((if e.start ≤ k.val ∧ k.val < e.start + e.span then 1 else 0) : ℚ)) : ℝ) =
        if e.start ≤ k.val ∧ k.val < e.start + e.span then 1 else 0 := by
    intro k
    by_cases hk : e.start ≤ k.val ∧ k.val < e.start + e.span <;> simp [hk]
  simp_rw [hcast]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun t ht => ⟨t, ?_⟩) ?_ ?_ ?_ ?_
  · rw [Finset.mem_Ico] at ht
    omega
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [Finset.mem_Ico] using ht
  · intro a ha b hb hab
    exact Fin.ext_iff.mp hab
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨k.val, by simpa [Finset.mem_Ico] using hk, Fin.ext rfl⟩
  · intro t ht
    have ht6 : t < 6 := by rw [Finset.mem_Ico] at ht; omega
    simp [Aggregation.gext, ht6]

private theorem term_quadratic_le (table : SparseTable)
    (htable : table.check = true) (e : Evidence) (p : TangentPayload 6)
    (box : Box 6) (hp : p.check (grid := 4000) box = true)
    (he : e.check table box = true) (x d : Fin 6 → ℝ) (hx : InBox p x) :
    dotProduct d (castMatrix (HessianTerm.matrix (termOfEvidence e)) *ᵥ d) ≤
      Weighted.pairWeight e.start (e.start + e.span) *
        CurrentKernelTotalDerivatives.closedWeightD2Total
          (realSpan x e.start e.span) * (realSpan d e.start e.span) ^ 2 := by
  have he0 := he
  rw [Evidence.check, Bool.and_eq_true] at he
  have hg := of_decide_eq_true he.2
  have hcurv := e.secondDerivative_sound_inBox table htable p box hp he0 x hx
  rw [rankOne_quadratic]
  change ((termOfEvidence e).coefficient : ℝ) *
      (∑ k, ((termOfEvidence e).direction k : ℝ) * d k) ^ 2 ≤ _
  rw [direction_sum_eq_span e d hg.2.1]
  have hcoeff : ((termOfEvidence e).coefficient : ℝ) =
      Weighted.pairWeight e.start (e.start + e.span) * (e.query.lower : ℝ) := by
    simp [termOfEvidence, Weighted.pairWeight]
  rw [hcoeff]
  gcongr
  exact Weighted.pairWeight_nonneg _ _

private lemma quadratic_hessian_eq_sum (terms : List (HessianTerm 6))
    (d : Fin 6 → ℝ) :
    dotProduct d (castMatrix (hessianMatrix terms) *ᵥ d) =
      (terms.map fun t => dotProduct d (castMatrix t.matrix *ᵥ d)).sum := by
  classical
  induction terms with
  | nil => simp [hessianMatrix, castMatrix, Matrix.mulVec, dotProduct]
  | cons t ts ih =>
      have hcast : castMatrix (hessianMatrix (t :: ts)) =
          castMatrix t.matrix + castMatrix (hessianMatrix ts) := by
        ext i j
        simp [castMatrix, hessianMatrix]
      rw [hcast, Matrix.add_mulVec, dotProduct_add, ih]
      simp

private def rowTerm (e : Evidence) (x d : Fin 6 → ℝ) : ℝ :=
  Weighted.pairWeight e.start (e.start + e.span) *
    CurrentKernelTotalDerivatives.closedWeightD2Total (realSpan x e.start e.span) *
    (realSpan d e.start e.span) ^ 2

private lemma rows_quadratic_le (table : SparseTable)
    (htable : table.check = true) (c : CompactRange.Certificate) (box : Box 6)
    (hcheck : c.check table box = true) (x d : Fin 6 → ℝ)
    (hx : InBox c.payload x) :
    dotProduct d (castMatrix (hessianMatrix c.payload.hessianTerms) *ᵥ d) ≤
      (c.ranges.map fun e => rowTerm e x d).sum := by
  rw [c.check_terms hcheck, quadratic_hessian_eq_sum]
  simp only [List.map_map]
  have hf := hcheck
  rw [CompactRange.Certificate.check, Bool.and_eq_true, Bool.and_eq_true] at hf
  have hp := hf.1.1
  have hrs := List.all_eq_true.mp hf.1.2
  apply List.sum_le_sum
  intro e he
  exact term_quadratic_le table htable e c.payload box hp (hrs e he) x d hx

private lemma canonical_rows_eq_lineSecond (table : SparseTable)
    (c : CompactRange.Certificate) (box : Box 6) (hcheck : c.check table box = true)
    (x d : Fin 6 → ℝ) :
    (c.ranges.map fun e => rowTerm e x d).sum =
      ∑ r ∈ Finset.Icc (1 : ℕ) 6,
        ∑ i ∈ Finset.range (7 - r),
          Weighted.pairWeight i (i + r) *
            CurrentKernelTotalDerivatives.closedWeightD2Total (realSpan x i r) *
            (realSpan d i r) ^ 2 := by
  have hs := c.check_support hcheck
  unfold CompactRange.Certificate.rangeKeys at hs
  change (c.ranges.map fun e => (e.start, e.span)) = Local.canonicalRangeKeys at hs
  have hmap : c.ranges.map (fun e => rowTerm e x d) =
      (c.ranges.map fun e => (e.start, e.span)).map
        (fun key => Weighted.pairWeight key.1 (key.1 + key.2) *
          CurrentKernelTotalDerivatives.closedWeightD2Total
            (realSpan x key.1 key.2) * (realSpan d key.1 key.2) ^ 2) := by
    simp [rowTerm, Function.comp_def]
  rw [hmap, hs]
  norm_num [Local.canonicalRangeKeys, Weighted.pairWeight,
    Weighted.pairWeightNumerator, Finset.sum_range_succ,
    Finset.sum_Icc_succ_top]
  ring

theorem lineSecond_lower (table : SparseTable) (htable : table.check = true)
    (c : CompactRange.Certificate) (box : Box 6) (hcheck : c.check table box = true)
    (x : Fin 6 → ℝ) (_hx : InBox c.payload x) (t : ℝ)
    (_ht : t ∈ interior (Icc (0 : ℝ) 1))
    (hpath : InBox c.payload (path c.payload x t)) :
    dotProduct (delta c.payload x)
        (castMatrix (hessianMatrix c.payload.hessianTerms) *ᵥ delta c.payload x) ≤
      lineSecond c.payload x t := by
  have hrows := rows_quadratic_le table htable c box hcheck
    (path c.payload x t) (delta c.payload x) hpath
  rw [canonical_rows_eq_lineSecond table c box hcheck] at hrows
  simpa [lineSecond, spanDelta] using hrows

/-- Only the seven scalar enclosures remain leaf-specific. -/
structure CertificateInputs (c : CompactRange.Certificate) where
  value_mem : (c.payload.value.lower : ℝ) ≤
    Weighted.F6 CurrentWindow.weight (fun i => c.payload.center i)
  gradient_mem : ∀ i,
    ((c.payload.gradient i).lower : ℝ) ≤
        CurrentAssembly.gradient (fun j => c.payload.center j) i ∧
      CurrentAssembly.gradient (fun j => c.payload.center j) i ≤
        (c.payload.gradient i).upper

/-- A range-free legacy shell is used only to reuse the already audited
calculus constructor, which depends solely on `payload`; it is never checked
or replayed. -/
private def shell (c : CompactRange.Certificate) : Local.Certificate :=
  { payload := c.payload, ranges := [] }

def producerInputs (table : SparseTable) (htable : table.check = true)
    (c : CompactRange.Certificate) (box : Box 6) (hcheck : c.check table box = true)
    (input : CertificateInputs c) :
    CurrentSemantics.ProducerInputs (shell c) box where
  gradient := CurrentAssembly.gradient
  value_mem := input.value_mem
  gradient_mem := input.gradient_mem
  gradient_zero := fun x _ => CurrentAssembly.gradient_zero c.payload x
  lineSecond_lower := fun x hx t ht hpath =>
    lineSecond_lower table htable c box hcheck x hx t ht hpath

/-- Exact current semantics for a compact certificate. -/
def semantics (table : SparseTable) (htable : table.check = true)
    (c : CompactRange.Certificate) (box : Box 6) (hcheck : c.check table box = true)
    (input : CertificateInputs c) : Local.Semantics c.payload :=
  (CurrentSemantics.ofProducerInputs (shell c) box
    (producerInputs table htable c box hcheck input)).toLocal

/-- Compact checked tangent leaf proves the exact current local inequality. -/
theorem current_sound (table : SparseTable) (htable : table.check = true)
    (c : CompactRange.Certificate) (box : Box 6) (hcheck : c.check table box = true)
    (input : CertificateInputs c) (point : CurrentGapVector)
    (hbox : box.Contains (locateGaps 4000 point)) :
    Weighted.beta ≤ Weighted.F6 CurrentWindow.weight point.1 := by
  have h := Local.sound c.payload (semantics table htable c box hcheck input)
    box (by
      have hf := hcheck
      rw [CompactRange.Certificate.check, Bool.and_eq_true, Bool.and_eq_true] at hf
      exact hf.1.1) point hbox
  have ht := c.check_target hcheck
  have htR : (c.payload.target : ℝ) = Weighted.beta := by
    rw [ht]
    norm_num [Weighted.beta]
  rw [← htR]
  exact h

end Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactHessian

end
