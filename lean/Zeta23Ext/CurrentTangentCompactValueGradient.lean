/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentValueGradientChecker
import Zeta23Ext.CurrentTangentCurvatureRMQ

/-!
# Compact shared-table value and gradient witnesses

The full center checker stores a semantic current-kernel cell at each of its
twenty-one pair spans.  Production leaves instead store only indices into the
same globally checked cell table used by curvature RMQ.  This module proves
that one global table check promotes every compact leaf to the existing full
value/gradient theorem; no transcendental row is rechecked per leaf.
-/

noncomputable section

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactValueGradient

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CurvatureRMQ

/-- A semantic cell reference.  The `Fin` bound is established by the strict
decoder and stores only the cell-table index at runtime. -/
structure SpanRef (table : CellTable) where
  index : Fin table.count

def SpanRef.globalCell {table : CellTable} (r : SpanRef table) : ℕ :=
  table.first + r.index.val

def SpanRef.toFull {table : CellTable} (r : SpanRef table) :
    Zeta23Ext.CurrentTangentValueGradientChecker.SpanWitness where
  kernel := table.cells r.index

def SpanRef.check {table : CellTable} (r : SpanRef table)
    (center : Fin 6 → ℚ) (i span : ℕ) : Bool :=
  decide (1 ≤ span ∧ i + span ≤ 6 ∧
    (r.globalCell : ℚ) / 4000 ≤
      Zeta23Ext.CurrentTangentValueGradientChecker.spanQ center i span ∧
    Zeta23Ext.CurrentTangentValueGradientChecker.spanQ center i span ≤
      (r.globalCell + 1 : ℕ) / 4000)

private lemma span_toFull_check {table : CellTable} (htable : table.check = true)
    {r : SpanRef table} {center : Fin 6 → ℚ} {i span : ℕ}
    (h : r.check center i span = true) :
    r.toFull.check center i span = true := by
  classical
  have ht : ∀ k, (table.cells k).check = true ∧
      (table.cells k).cell = table.first + k.val := by
    simpa [CellTable.check] using of_decide_eq_true htable
  have hg : 1 ≤ span ∧ i + span ≤ 6 ∧
      (r.globalCell : ℚ) / 4000 ≤
        Zeta23Ext.CurrentTangentValueGradientChecker.spanQ center i span ∧
      Zeta23Ext.CurrentTangentValueGradientChecker.spanQ center i span ≤
        (r.globalCell + 1 : ℕ) / 4000 := by
    exact of_decide_eq_true h
  rw [Zeta23Ext.CurrentTangentValueGradientChecker.SpanWitness.check,
    Bool.and_eq_true]
  refine ⟨(ht r.index).1, ?_⟩
  apply decide_eq_true
  simpa [SpanRef.toFull, SpanRef.globalCell, (ht r.index).2] using hg

/-- A center leaf containing 21 bounded table indices and seven reported
intervals. -/
structure Witness (table : CellTable) where
  center : Fin 6 → ℚ
  span : ℕ → ℕ → SpanRef table
  reportedValue : CurrentWeightD2CellChecker.QInterval
  reportedGradient : Fin 6 → CurrentWeightD2CellChecker.QInterval

def Witness.toFull {table : CellTable} (w : Witness table) :
    Zeta23Ext.CurrentTangentValueGradientChecker.Witness where
  center := w.center
  span i r := (w.span i r).toFull
  reportedValue := w.reportedValue
  reportedGradient := w.reportedGradient

/-- Leaf-only checker: it checks 21 index/geometry joins and rational interval
arithmetic, but deliberately does not recheck semantic cells. -/
noncomputable def Witness.Check {table : CellTable} (w : Witness table) : Prop :=
  (∀ r ∈ Finset.Icc (1 : ℕ) 6, ∀ i ∈ Finset.range (7 - r),
    (w.span i r).check w.center i r = true) ∧
  w.reportedValue.lo ≤
      (Zeta23Ext.CurrentTangentValueGradientChecker.objectiveInterval
        w.center (fun i r => (w.span i r).toFull)).lo ∧
  (Zeta23Ext.CurrentTangentValueGradientChecker.objectiveInterval
      w.center (fun i r => (w.span i r).toFull)).hi ≤
    w.reportedValue.hi ∧
  ∀ k,
    (w.reportedGradient k).lo ≤
      (Zeta23Ext.CurrentTangentValueGradientChecker.gradientInterval
        w.center (fun i r => (w.span i r).toFull) k).lo ∧
    (Zeta23Ext.CurrentTangentValueGradientChecker.gradientInterval
        w.center (fun i r => (w.span i r).toFull) k).hi ≤
      (w.reportedGradient k).hi

noncomputable def Witness.check {table : CellTable} (w : Witness table) : Bool := by
  classical
  exact decide w.Check

private lemma witness_check_facts {table : CellTable} {w : Witness table}
    (h : w.check = true) : w.Check := by
  classical
  exact of_decide_eq_true (show decide w.Check = true by
    simpa only [Witness.check] using h)

private lemma toFull_check {table : CellTable} (htable : table.check = true)
    (w : Witness table) (h : w.check = true) : w.toFull.check = true := by
  classical
  have hf := witness_check_facts h
  apply decide_eq_true
  refine ⟨?_, hf.2⟩
  intro r hr i hi
  exact span_toFull_check htable (hf.1 r hr i hi)

/-- One global semantic table check plus a compact leaf check proves the exact
current objective value and six gradient enclosures. -/
theorem Witness.sound {table : CellTable} (htable : table.check = true)
    (w : Witness table) (h : w.check = true) :
    w.reportedValue.Mem
      (Weighted.F6 CurrentWindow.weight (fun i => (w.center i : ℝ))) ∧
    ∀ k, (w.reportedGradient k).Mem
      (Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentAssembly.gradient
        (fun i => (w.center i : ℝ)) k) := by
  exact w.toFull.sound (toFull_check htable w h)

end Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactValueGradient

end
