/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentCurrentHessian

/-!
# Full checked Hessian assembly for current tangent leaves

This module sums the individually semantic range rows and uses the checked
canonical 20-key support to identify that sum with the full nonzero pair sum
in the current objective.
-/

noncomputable section

open Set Matrix
open scoped BigOperators

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentHessianAssembly

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay
open Zeta23Ext.VerifiedCertificate.CurrentTangent
open Zeta23Ext.VerifiedCertificate.CurrentTangent.Local
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentSemantics
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentHessian

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

private def rowTerm (e : CurrentTangent.Range.Evidence)
    (x d : Fin 6 → ℝ) : ℝ :=
  Weighted.pairWeight e.geometry.start
      (e.geometry.start + e.geometry.span) *
    CurrentKernelTotalDerivatives.closedWeightD2Total
      (realSpan x e.geometry.start e.geometry.span) *
    (realSpan d e.geometry.start e.geometry.span) ^ 2

private lemma rows_quadratic_le (c : Local.Certificate) (box : Box 6)
    (hcheck : c.check box = true) (x d : Fin 6 → ℝ)
    (hx : InBox c.payload x) :
    dotProduct d (castMatrix (hessianMatrix c.payload.hessianTerms) *ᵥ d) ≤
      (c.ranges.map fun e => rowTerm e x d).sum := by
  rw [c.check_terms hcheck, quadratic_hessian_eq_sum]
  simp only [List.map_map, Function.comp_apply]
  have hf := hcheck
  rw [Local.Certificate.check, Bool.and_eq_true, Bool.and_eq_true] at hf
  have hp := hf.1.1
  have hrs := List.all_eq_true.mp hf.1.2
  apply List.sum_le_sum
  intro e he
  exact termOfRange_quadratic_le e c.payload box hp (hrs e he) x d hx

/- The ordered support theorem reduces this goal to twenty explicit rows.
Keeping this lemma separate makes the generated-data interface clear: no
analytic fact remains here, only exact list/key bookkeeping. -/
private lemma canonical_rows_eq_lineSecond (c : Local.Certificate)
    (box : Box 6) (hcheck : c.check box = true) (x d : Fin 6 → ℝ) :
    (c.ranges.map fun e => rowTerm e x d).sum =
      ∑ r ∈ Finset.Icc (1 : ℕ) 6,
        ∑ i ∈ Finset.range (7 - r),
          Weighted.pairWeight i (i + r) *
            CurrentKernelTotalDerivatives.closedWeightD2Total (realSpan x i r) *
            (realSpan d i r) ^ 2 := by
  have hs := c.check_support hcheck
  -- The support list contains the 20 nonzero pairs exactly once; `(1,5)` is
  -- the sole missing pair and has definitionally zero weight.
  unfold Local.Certificate.rangeKeys at hs
  change (c.ranges.map fun e => (e.geometry.start, e.geometry.span)) =
    Local.canonicalRangeKeys at hs
  -- Rewrite the sum through the ordered key equality.  `rowTerm` depends only
  -- on the key, so no witness metadata survives this step.
  have hmap : c.ranges.map (fun e => rowTerm e x d) =
      (c.ranges.map fun e => (e.geometry.start, e.geometry.span)).map
        (fun key => Weighted.pairWeight key.1 (key.1 + key.2) *
          CurrentKernelTotalDerivatives.closedWeightD2Total
            (realSpan x key.1 key.2) * (realSpan d key.1 key.2) ^ 2) := by
    simp [rowTerm, Function.comp_def]
  rw [hmap, hs]
  norm_num [Local.canonicalRangeKeys, Weighted.pairWeight,
    Weighted.pairWeightNumerator, Finset.sum_range_succ,
    Finset.sum_Icc_succ_top]
  ring

/-- All 20 checked nonzero range rows assemble into the exact second-line
derivative lower bound. -/
theorem lineSecond_lower (c : Local.Certificate) (box : Box 6)
    (hcheck : c.check box = true) (x : Fin 6 → ℝ)
    (hx : InBox c.payload x) (t : ℝ)
    (_ht : t ∈ interior (Icc (0 : ℝ) 1))
    (hpath : InBox c.payload (path c.payload x t)) :
    dotProduct (delta c.payload x)
        (castMatrix (hessianMatrix c.payload.hessianTerms) *ᵥ
          delta c.payload x) ≤ lineSecond c.payload x t := by
  have hrows := rows_quadratic_le c box hcheck (path c.payload x t)
    (delta c.payload x) hpath
  rw [canonical_rows_eq_lineSecond c box hcheck] at hrows
  simpa [lineSecond, spanDelta] using hrows

/-- The final numerical producer inputs after both finite derivative seams
have been discharged: one center-value enclosure and six gradient
enclosures. -/
structure CertificateInputs (c : Local.Certificate) where
  value_mem : (c.payload.value.lower : ℝ) ≤
    Weighted.F6 CurrentWindow.weight (fun i => c.payload.center i)
  gradient_mem : ∀ i,
    ((c.payload.gradient i).lower : ℝ) ≤
        CurrentAssembly.gradient (fun j => c.payload.center j) i ∧
      CurrentAssembly.gradient (fun j => c.payload.center j) i ≤
        (c.payload.gradient i).upper

/-- A checked 20-row certificate plus the seven scalar enclosures constructs
the complete audited current-semantics producer package. -/
def producerInputs (c : Local.Certificate) (box : Box 6)
    (hcheck : c.check box = true) (input : CertificateInputs c) :
    CurrentSemantics.ProducerInputs c box where
  gradient := CurrentAssembly.gradient
  value_mem := input.value_mem
  gradient_mem := input.gradient_mem
  gradient_zero := fun x _ => CurrentAssembly.gradient_zero c.payload x
  lineSecond_lower := fun x _ t ht hpath =>
    lineSecond_lower c box hcheck x (by assumption) t ht hpath

end Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentHessianAssembly

end
