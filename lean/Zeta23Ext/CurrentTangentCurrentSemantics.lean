/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentLocalPayload

/-!
# Current-objective tangent semantics

This module removes the derivative part of the tangent-leaf producer seam.
The objective is definitionally the exact current `Weighted.F6`; its first and
second derivatives along a center-to-point line are assembled from the
all-real total derivatives of `CurrentWindow.weight`.

The remaining `ProducerInputs` are exactly the numerical interval facts and
the Hessian comparison assembled from the checked wide-range rows.  In
particular, a producer no longer supplies arbitrary line derivative theorems.
-/

noncomputable section

open Set
open scoped BigOperators

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentSemantics

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay
open Zeta23Ext.VerifiedCertificate.CurrentTangent
open Zeta23Ext.VerifiedCertificate.CurrentTangent.Local

def path (p : TangentPayload 6) (x : Fin 6 → ℝ) (t : ℝ) : Fin 6 → ℝ :=
  fun i => (p.center i : ℝ) + t * (x i - (p.center i : ℝ))

def delta (p : TangentPayload 6) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun i => x i - (p.center i : ℝ)

def spanDelta (p : TangentPayload 6) (x : Fin 6 → ℝ)
    (i r : ℕ) : ℝ := realSpan (delta p x) i r

def lineFirst (p : TangentPayload 6) (x : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  Weighted.pressure * ∑ i, delta p x i +
    ∑ r ∈ Finset.Icc (1 : ℕ) 6,
      ∑ i ∈ Finset.range (7 - r),
        Weighted.pairWeight i (i + r) *
          CurrentKernelTotalDerivatives.closedWeightD1Total
            (realSpan (path p x t) i r) * spanDelta p x i r

def lineSecond (p : TangentPayload 6) (x : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc (1 : ℕ) 6,
    ∑ i ∈ Finset.range (7 - r),
      Weighted.pairWeight i (i + r) *
        CurrentKernelTotalDerivatives.closedWeightD2Total
          (realSpan (path p x t) i r) * spanDelta p x i r ^ 2

private lemma hasDerivAt_path_coordinate (p : TangentPayload 6)
    (x : Fin 6 → ℝ) (t : ℝ) (i : Fin 6) :
    HasDerivAt (fun u => path p x u i) (delta p x i) t := by
  change HasDerivAt
    (fun u => (p.center i : ℝ) + u * (x i - (p.center i : ℝ)))
    (x i - (p.center i : ℝ)) t
  simpa only [id_eq, one_mul] using
    ((hasDerivAt_id t).mul_const
      (x i - (p.center i : ℝ))).const_add (p.center i : ℝ)

private lemma hasDerivAt_gapSum (p : TangentPayload 6)
    (x : Fin 6 → ℝ) (t : ℝ) :
    HasDerivAt (fun u => ∑ i, path p x u i) (∑ i, delta p x i) t := by
  apply HasDerivAt.fun_sum
  intro i _
  exact hasDerivAt_path_coordinate p x t i

private lemma hasDerivAt_realSpan_path (p : TangentPayload 6)
    (x : Fin 6 → ℝ) (t : ℝ) (i r : ℕ) :
    HasDerivAt (fun u => realSpan (path p x u) i r) (spanDelta p x i r) t := by
  unfold realSpan spanDelta
  apply HasDerivAt.fun_sum
  intro k _
  by_cases hk : k < 6
  · simp only [Aggregation.gext, hk, path, delta]
    change HasDerivAt
      (fun u => (p.center ⟨k, hk⟩ : ℝ) +
        u * (x ⟨k, hk⟩ - (p.center ⟨k, hk⟩ : ℝ)))
      (x ⟨k, hk⟩ - (p.center ⟨k, hk⟩ : ℝ)) t
    exact hasDerivAt_path_coordinate p x t ⟨k, hk⟩
  · simp only [Aggregation.gext, hk]
    exact hasDerivAt_const t 0

theorem hasDerivAt_objective_line (p : TangentPayload 6)
    (x : Fin 6 → ℝ) (t : ℝ) :
    HasDerivAt
      (fun u => Weighted.F6 CurrentWindow.weight (path p x u))
      (lineFirst p x t) t := by
  unfold Weighted.F6 Weighted.F6With lineFirst
  apply (hasDerivAt_gapSum p x t).const_mul Weighted.pressure |>.add
  apply HasDerivAt.fun_sum
  intro r _
  apply HasDerivAt.fun_sum
  intro i _
  have hw := (CurrentKernelTotalDerivatives.hasDerivAt_currentWeight
    (realSpan (path p x t) i r)).comp t (hasDerivAt_realSpan_path p x t i r)
  have h := hw.const_mul (Weighted.pairWeight i (i + r))
  have h' := h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  apply h'.congr_deriv
  ring

theorem hasDerivAt_lineFirst (p : TangentPayload 6)
    (x : Fin 6 → ℝ) (t : ℝ) :
    HasDerivAt (lineFirst p x) (lineSecond p x t) t := by
  unfold lineFirst lineSecond
  have hpairs : HasDerivAt
      (fun t => ∑ r ∈ Finset.Icc (1 : ℕ) 6,
        ∑ i ∈ Finset.range (7 - r),
          Weighted.pairWeight i (i + r) *
              CurrentKernelTotalDerivatives.closedWeightD1Total
                (realSpan (path p x t) i r) * spanDelta p x i r)
      (∑ r ∈ Finset.Icc (1 : ℕ) 6,
        ∑ i ∈ Finset.range (7 - r),
          Weighted.pairWeight i (i + r) *
            CurrentKernelTotalDerivatives.closedWeightD2Total
              (realSpan (path p x t) i r) * spanDelta p x i r ^ 2) t := by
    apply HasDerivAt.fun_sum
    intro r _
    apply HasDerivAt.fun_sum
    intro i _
    have hw := (CurrentKernelTotalDerivatives.hasDerivAt_currentWeightD1
      (realSpan (path p x t) i r)).comp t (hasDerivAt_realSpan_path p x t i r)
    have h := (hw.const_mul (Weighted.pairWeight i (i + r))).mul_const
      (spanDelta p x i r)
    apply h.congr_deriv
    ring
  simpa only using hpairs.const_add
    (Weighted.pressure * ∑ i, delta p x i)

/-- The only remaining inputs after total derivative assembly.  `gradient_zero`
is finite first-derivative bookkeeping.  `lineSecond_lower` is the precise
wide-range Hessian comparison: its segment-membership premise prevents a
leaf certificate from being used globally. -/
structure ProducerInputs (c : Local.Certificate) (box : Box 6) where
  gradient : (Fin 6 → ℝ) → Fin 6 → ℝ
  value_mem : (c.payload.value.lower : ℝ) ≤
    Weighted.F6 CurrentWindow.weight (fun i => c.payload.center i)
  gradient_mem : ∀ i,
    ((c.payload.gradient i).lower : ℝ) ≤
        gradient (fun j => c.payload.center j) i ∧
      gradient (fun j => c.payload.center j) i ≤
        (c.payload.gradient i).upper
  gradient_zero : ∀ x : Fin 6 → ℝ, InBox c.payload x →
    lineFirst c.payload x 0 =
      ∑ i, gradient (fun j => c.payload.center j) i * delta c.payload x i
  lineSecond_lower : ∀ (x : Fin 6 → ℝ), InBox c.payload x → ∀ t,
    t ∈ interior (Icc (0 : ℝ) 1) →
    InBox c.payload (path c.payload x t) →
    dotProduct (delta c.payload x)
        (Matrix.mulVec (castMatrix (hessianMatrix c.payload.hessianTerms))
          (delta c.payload x)) ≤
      lineSecond c.payload x t

/-- Actual current-specific semantics constructor.  All differentiability and
continuity fields are discharged from the all-real kernel derivative theorem;
the producer cannot choose a different objective or line derivative. -/
def ofProducerInputs (c : Local.Certificate) (box : Box 6)
    (input : ProducerInputs c box) : Local.CurrentSemantics c box where
  toLocal := {
    objective := Weighted.F6 CurrentWindow.weight
    gradient := input.gradient
    lineFirst := lineFirst c.payload
    lineSecond := lineSecond c.payload
    value_mem := input.value_mem
    gradient_mem := input.gradient_mem
    continuous_line := fun x _ => by
      have hc : Continuous
          (fun t => Weighted.F6 CurrentWindow.weight (path c.payload x t)) :=
        continuous_iff_continuousAt.mpr fun t =>
          (hasDerivAt_objective_line c.payload x t).continuousAt
      exact hc.continuousOn
    hasLineFirst := fun x _ t _ =>
      (hasDerivAt_objective_line c.payload x t).hasDerivWithinAt
    hasLineSecond := fun x _ t _ =>
      (hasDerivAt_lineFirst c.payload x t).hasDerivWithinAt
    lineSecond_lower := input.lineSecond_lower
    hasLineDerivZero := fun x hx => by
      change HasDerivAt (fun t => Weighted.F6 CurrentWindow.weight
        (path c.payload x t)) _ 0
      convert hasDerivAt_objective_line c.payload x 0 using 1
      exact (input.gradient_zero x hx).symm
  }
  objective_eq := fun _ => rfl

end Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentSemantics

end
