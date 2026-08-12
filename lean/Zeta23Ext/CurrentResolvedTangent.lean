/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentCompactValueGradient
import Zeta23Ext.CurrentTangentCompactHessianAssembly

/-!
# Resolved compact tangent adapter

This module joins the three independently checked parts of one production
tangent leaf: its rational payload, the current-weight value/gradient
witness at its center, and the globally shared RMQ-backed curvature table.
Every join is an executable rational equality.  The resulting leaf theorem
has no theorem-valued numerical premise.
-/

noncomputable section

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.Resolved

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay
open Zeta23Ext.VerifiedCertificate.CurrentTangent
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CurvatureRMQ

abbrev CompactCertificate :=
  Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactRange.Certificate

/-- One compact tangent leaf plus its independently checked center data. -/
structure Certificate (table : SparseTable) where
  compact : CompactCertificate
  centerData :
    Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactValueGradient.Witness
      table.cells

/-- Acceptance links the center and all seven reported intervals to the
payload that is actually replayed. -/
noncomputable def Certificate.check {table : SparseTable} (c : Certificate table)
    (box : Box 6) : Bool := by
  classical
  exact c.compact.check table box && c.centerData.check && decide
    (c.centerData.center = c.compact.payload.center ∧
      c.centerData.reportedValue.lo = c.compact.payload.value.lower ∧
      c.centerData.reportedValue.hi = c.compact.payload.value.upper ∧
      ∀ i : Fin 6,
        (c.centerData.reportedGradient i).lo =
          (c.compact.payload.gradient i).lower ∧
        (c.centerData.reportedGradient i).hi =
          (c.compact.payload.gradient i).upper)

private lemma check_facts {table : SparseTable} {c : Certificate table} {box : Box 6}
    (h : c.check box = true) :
    c.compact.check table box = true ∧ c.centerData.check = true ∧
      c.centerData.center = c.compact.payload.center ∧
      c.centerData.reportedValue.lo = c.compact.payload.value.lower ∧
      c.centerData.reportedValue.hi = c.compact.payload.value.upper ∧
      ∀ i : Fin 6,
        (c.centerData.reportedGradient i).lo =
          (c.compact.payload.gradient i).lower ∧
        (c.centerData.reportedGradient i).hi =
          (c.compact.payload.gradient i).upper := by
  rw [Certificate.check, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, of_decide_eq_true h.2⟩

private theorem scalarInputs (table : SparseTable) (htable : table.check = true)
    (c : Certificate table) (box : Box 6) (hcheck : c.check box = true) :
    Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactHessian.CertificateInputs
      c.compact := by
  have hf := check_facts hcheck
  have hcenter := c.centerData.sound (by
    exact (show table.cells.check = true from by
      rw [SparseTable.check, Bool.and_eq_true] at htable
      exact htable.1)) hf.2.1
  refine { value_mem := ?_, gradient_mem := ?_ }
  · rw [← hf.2.2.2.1, ← hf.2.2.1]
    exact hcenter.1.1
  · intro i
    have hi := hcenter.2 i
    rw [← (hf.2.2.2.2.2 i).1, ← hf.2.2.1]
    rw [← (hf.2.2.2.2.2 i).2]
    exact hi

/-- End-to-end leaf theorem exposed to finite replay.  The shared sparse
table is checked once by `htable`; compact-range, payload, center-value,
gradient, LDL, and cross-link checks remain leaf-local Boolean obligations. -/
theorem sound (table : SparseTable) (htable : table.check = true)
    (c : Certificate table) (box : Box 6) (hcheck : c.check box = true)
    (point : CurrentGapVector)
    (hbox : box.Contains (locateGaps 4000 point)) :
    Weighted.beta ≤ Weighted.F6 CurrentWindow.weight point.1 := by
  have hf := check_facts hcheck
  exact Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactHessian.current_sound
    table htable c.compact box hf.1 (scalarInputs table htable c box hcheck)
      point hbox

end Zeta23Ext.VerifiedCertificate.CurrentTangent.Resolved

end
