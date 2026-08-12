/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentCurrentSemantics

/-!
# Canonical finite assembly for current tangent semantics

This module discharges the first-derivative bookkeeping seam without changing
the audited analytic semantics module.  The coordinate gradient below is the
literal derivative of the current weighted six-gap objective.  Its pairing
with a displacement is proved by generic finite-sum exchange.
-/

noncomputable section

open Set Matrix
open scoped BigOperators

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentAssembly

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay
open Zeta23Ext.VerifiedCertificate.CurrentTangent
open Zeta23Ext.VerifiedCertificate.CurrentTangent.Local
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentSemantics

/-- Literal coordinate gradient of the current six-gap objective. -/
def gradient (g : Fin 6 → ℝ) (k : Fin 6) : ℝ :=
  Weighted.pressure +
    ∑ r ∈ Finset.Icc (1 : ℕ) 6,
      ∑ i ∈ Finset.range (7 - r),
        if k.val ∈ Finset.Ico i (i + r) then
          Weighted.pairWeight i (i + r) *
            CurrentKernelTotalDerivatives.closedWeightD1Total (realSpan g i r)
        else 0

private lemma realSpan_eq_fin_sum (g : Fin 6 → ℝ) (i r : ℕ)
    (hir : i + r ≤ 6) :
    realSpan g i r =
      ∑ k : Fin 6, if k.val ∈ Finset.Ico i (i + r) then g k else 0 := by
  classical
  unfold realSpan
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun t ht => ⟨t, ?_⟩) ?_ ?_ ?_ ?_
  · rw [Finset.mem_Ico] at ht
    omega
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ht
  · intro a ha b hb hab
    exact Fin.ext_iff.mp hab
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨k.val, hk, Fin.ext rfl⟩
  · intro t ht
    have ht6 : t < 6 := by
      rw [Finset.mem_Ico] at ht
      omega
    simp [Aggregation.gext, ht6]

private lemma path_zero (p : TangentPayload 6) (x : Fin 6 → ℝ) :
    path p x 0 = fun i => (p.center i : ℝ) := by
  funext i
  simp [path]

/-- Generic distributivity/exchange identity used to turn span directional
derivatives into the dot product with the coordinate gradient. -/
private lemma exchange_pair_spans (d : Fin 6 → ℝ)
    (A : ℕ → ℕ → ℝ) :
    (∑ r ∈ Finset.Icc (1 : ℕ) 6,
      ∑ i ∈ Finset.range (7 - r),
        A r i * (∑ k : Fin 6,
          if k.val ∈ Finset.Ico i (i + r) then d k else 0)) =
      ∑ k : Fin 6,
        (∑ r ∈ Finset.Icc (1 : ℕ) 6,
          ∑ i ∈ Finset.range (7 - r),
            if k.val ∈ Finset.Ico i (i + r) then A r i else 0) * d k := by
  calc
    _ = ∑ r ∈ Finset.Icc (1 : ℕ) 6,
        ∑ k : Fin 6, ∑ i ∈ Finset.range (7 - r),
          if k.val ∈ Finset.Ico i (i + r) then A r i * d k else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
    _ = ∑ k : Fin 6, ∑ r ∈ Finset.Icc (1 : ℕ) 6,
        ∑ i ∈ Finset.range (7 - r),
          if k.val ∈ Finset.Ico i (i + r) then A r i * d k else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      simp_rw [Finset.sum_mul, ite_mul, zero_mul]

/-- The canonical gradient pairing is exactly the first line derivative at
the payload center.  No box premise or numerical input is needed. -/
theorem gradient_zero (p : TangentPayload 6) (x : Fin 6 → ℝ) :
    lineFirst p x 0 =
      ∑ k, gradient (fun i => p.center i) k * delta p x k := by
  let A : ℕ → ℕ → ℝ := fun r i =>
    Weighted.pairWeight i (i + r) *
      CurrentKernelTotalDerivatives.closedWeightD1Total
        (realSpan (fun j => (p.center j : ℝ)) i r)
  have hspan : ∀ r ∈ Finset.Icc (1 : ℕ) 6,
      ∀ i ∈ Finset.range (7 - r),
        spanDelta p x i r = ∑ k : Fin 6,
          if k.val ∈ Finset.Ico i (i + r) then delta p x k else 0 := by
    intro r hr i hi
    apply realSpan_eq_fin_sum
    rw [Finset.mem_Icc] at hr
    rw [Finset.mem_range] at hi
    omega
  rw [lineFirst, path_zero]
  have hpairs :
      (∑ r ∈ Finset.Icc (1 : ℕ) 6,
        ∑ i ∈ Finset.range (7 - r),
          Weighted.pairWeight i (i + r) *
            CurrentKernelTotalDerivatives.closedWeightD1Total
              (realSpan (fun j => (p.center j : ℝ)) i r) * spanDelta p x i r) =
      ∑ r ∈ Finset.Icc (1 : ℕ) 6,
        ∑ i ∈ Finset.range (7 - r), A r i *
          (∑ k : Fin 6,
            if k.val ∈ Finset.Ico i (i + r) then delta p x k else 0) := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro i hi
    rw [hspan r hr i hi]
  rw [hpairs]
  change Weighted.pressure * ∑ i, delta p x i +
      ∑ r ∈ Finset.Icc (1 : ℕ) 6,
        ∑ i ∈ Finset.range (7 - r), A r i *
          (∑ k : Fin 6,
            if k.val ∈ Finset.Ico i (i + r) then delta p x k else 0) = _
  rw [exchange_pair_spans]
  simp_rw [gradient, add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- After canonical gradient assembly, the numerical producer is responsible
only for the center value, six gradient enclosures, and the local Hessian
comparison. -/
structure NumericalInputs (c : Local.Certificate) (box : Box 6) where
  value_mem : (c.payload.value.lower : ℝ) ≤
    Weighted.F6 CurrentWindow.weight (fun i => c.payload.center i)
  gradient_mem : ∀ i,
    ((c.payload.gradient i).lower : ℝ) ≤
        gradient (fun j => c.payload.center j) i ∧
      gradient (fun j => c.payload.center j) i ≤
        (c.payload.gradient i).upper
  lineSecond_lower : ∀ (x : Fin 6 → ℝ), InBox c.payload x → ∀ t,
    t ∈ interior (Icc (0 : ℝ) 1) →
    InBox c.payload (path c.payload x t) →
    dotProduct (delta c.payload x)
        (Matrix.mulVec (castMatrix (hessianMatrix c.payload.hessianTerms))
          (delta c.payload x)) ≤
      lineSecond c.payload x t

/-- Honest adapter to the audited producer seam: `gradient_zero` is supplied
by the theorem above, not by generated data. -/
def producerInputs (c : Local.Certificate) (box : Box 6)
    (input : NumericalInputs c box) : CurrentSemantics.ProducerInputs c box where
  gradient := gradient
  value_mem := input.value_mem
  gradient_mem := input.gradient_mem
  gradient_zero := fun x _ => gradient_zero c.payload x
  lineSecond_lower := input.lineSecond_lower

end Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentAssembly

end
