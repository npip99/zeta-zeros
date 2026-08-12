/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.VerifiedAnnotatedForest
import Zeta23Ext.CurrentCertificateReplay
import Zeta23Ext.ProductionCell4376Jets

/-!
# Concrete span-to-kernel-cell evidence for tangent leaves

The production tangent rule first needs to turn a six-gap integer box into
certified cells for every pair separation used in its Hessian.  This module
supplies that executable mapping layer.  It does not yet encode the full LDL
or affine tangent payload.

`KernelCellWitness` is deliberately an extensible semantic index rather than
a raw claimed number.  Every constructor must carry a theorem bounding the
actual current-window second derivative on its grid cell.
-/

noncomputable section

open Set

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay

/-- Kernel-checked second-derivative cells currently available to tangent
evidence.  More production cells can be generated as additional constructors.
-/
inductive KernelCellWitness where
  | cell4376
  deriving DecidableEq

def KernelCellWitness.cell : KernelCellWitness → ℕ
  | .cell4376 => 4376

def KernelCellWitness.lower : KernelCellWitness → ℝ
  | .cell4376 =>
      (CurrentKernelDerivatives.cell4376Lower : ℝ)

theorem KernelCellWitness.sound (w : KernelCellWitness) {x : ℝ}
    (hx : x ∈ Icc ((w.cell : ℝ) / 4000) ((w.cell + 1 : ℕ) / 4000)) :
    w.lower ≤ CurrentKernelDerivatives.closedWeightD2 x := by
  cases w
  exact ProductionCell4376Jets.cell4376_semantic hx

/-- One Hessian span obligation in a tangent leaf.  `start` and `span`
identify the consecutive gap sum, while `witness` identifies its semantic
kernel cell. -/
structure SpanEvidence where
  start : ℕ
  span : ℕ
  witness : KernelCellWitness
  deriving DecidableEq

/-- Exact finite check that every lattice point in `box` maps the indicated
real span into the single cell named by `witness`. -/
def SpanEvidence.check (e : SpanEvidence) (box : Box 6) : Bool :=
  decide (0 < e.span ∧ e.start + e.span ≤ 6 ∧
    e.witness.cell ≤ lowerSpan box e.start e.span ∧
    upperSpan box e.start e.span + e.span ≤ e.witness.cell + 1)

private lemma check_facts {e : SpanEvidence} {box : Box 6}
    (h : e.check box = true) :
    0 < e.span ∧ e.start + e.span ≤ 6 ∧
      e.witness.cell ≤ lowerSpan box e.start e.span ∧
      upperSpan box e.start e.span + e.span ≤ e.witness.cell + 1 := by
  simpa [SpanEvidence.check] using of_decide_eq_true h

/-- The executable span check has its intended real semantics: box membership
of the located six-gap vector places the corresponding real separation in
the certified closed kernel cell. -/
theorem SpanEvidence.realSpan_mem_cell (e : SpanEvidence) (box : Box 6)
    (hcheck : e.check box = true) (gaps : CurrentGapVector)
    (hbox : box.Contains (locateGaps 4000 gaps)) :
    realSpan gaps.1 e.start e.span ∈
      Icc ((e.witness.cell : ℝ) / 4000)
        ((e.witness.cell + 1 : ℕ) / 4000) := by
  obtain ⟨_, hvalid, hlo, hhi⟩ := check_facts hcheck
  have hcellLo := Box.lowerSpan_le_cellSpan hbox e.start e.span
  have hcellHi := Box.cellSpan_le_upperSpan hbox e.start e.span
  have hrealLo := cellSpan_lower (grid := 4000) (by norm_num) gaps hvalid
  have hrealHi := cellSpan_upper (grid := 4000) (by norm_num) gaps hvalid
  constructor
  · have hnat : e.witness.cell ≤ cellSpan (locateGaps 4000 gaps) e.start e.span :=
      hlo.trans hcellLo
    have hcast : (e.witness.cell : ℝ) ≤
        cellSpan (locateGaps 4000 gaps) e.start e.span := by exact_mod_cast hnat
    exact le_trans (div_le_div_of_nonneg_right hcast (by norm_num)) hrealLo
  · have hnat : cellSpan (locateGaps 4000 gaps) e.start e.span + e.span ≤
        e.witness.cell + 1 := by omega
    have hcast :
        ((cellSpan (locateGaps 4000 gaps) e.start e.span : ℕ) + e.span : ℝ) ≤
          (e.witness.cell + 1 : ℕ) := by exact_mod_cast hnat
    exact hrealHi.trans (div_le_div_of_nonneg_right hcast (by norm_num))

/-- A checked span witness yields the required semantic Hessian-term bound.
This is the interface the future LDL checker consumes. -/
theorem SpanEvidence.secondDerivative_sound (e : SpanEvidence) (box : Box 6)
    (hcheck : e.check box = true) (gaps : CurrentGapVector)
    (hbox : box.Contains (locateGaps 4000 gaps)) :
    e.witness.lower ≤
      CurrentKernelDerivatives.closedWeightD2
        (realSpan gaps.1 e.start e.span) :=
  e.witness.sound (e.realSpan_mem_cell box hcheck gaps hbox)

/-- Concrete annotated-forest predicate for a single span-to-cell Hessian
obligation. -/
def tangentOK (e : SpanEvidence) (box : Box 6) : Bool := e.check box

theorem tangentOK_sound (e : SpanEvidence) (box : Box 6)
    (hcheck : tangentOK e box = true) :
    ∀ gaps : CurrentGapVector, box.Contains (locateGaps 4000 gaps) →
      e.witness.lower ≤
        CurrentKernelDerivatives.closedWeightD2
          (realSpan gaps.1 e.start e.span) := by
  intro gaps hbox
  exact e.secondDerivative_sound box hcheck gaps hbox

/-! ## Small real annotated-leaf regression -/

namespace Demo

def evidence : SpanEvidence := ⟨0, 1, .cell4376⟩

def root : Box 6 where
  lo i := if i = 0 then 4376 else 0
  hi i := if i = 0 then 4376 else 0

/-- A deliberately impossible regular branch makes this demo exercise the
direct real tangent conclusion rather than integer-score transfer. -/
def problem : IntegerLowerBoundProblem 6 where
  target := 1
  exactScore := fun _ => 0
  lowerScore := fun _ => 0
  lowerScore_sound := by intros; omega

def tree : Annotated.Tree 6 SpanEvidence :=
  .leaf (.tangent evidence)

theorem evidence_checked : tangentOK evidence root = true := by
  norm_num [tangentOK, SpanEvidence.check, evidence, root, lowerSpan, upperSpan,
    cellExt, Finset.sum_Ico_eq_sub, KernelCellWitness.cell]

def demoTangentOK (e : SpanEvidence) (box : Box 6) : Bool :=
  decide (e = evidence) && tangentOK e box

theorem demoTangentOK_sound (e : SpanEvidence) (box : Box 6)
    (hcheck : demoTangentOK e box = true) :
    ∀ gaps : CurrentGapVector, box.Contains (locateGaps 4000 gaps) →
      (CurrentKernelDerivatives.cell4376Lower : ℝ) ≤
        CurrentKernelDerivatives.closedWeightD2 (realSpan gaps.1 0 1) := by
  rw [demoTangentOK, Bool.and_eq_true] at hcheck
  have he : e = evidence := by
    simpa using of_decide_eq_true hcheck.1
  subst e
  simpa [evidence, KernelCellWitness.lower] using
    tangentOK_sound evidence box hcheck.2

/-- End-to-end regression through `Annotated.Tree.check_sound`: a checked
real tangent leaf yields the semantic current-kernel curvature bound on the
gap represented by its six-dimensional root box. -/
theorem tree_sound (gaps : CurrentGapVector)
    (hroot : root.Contains (locateGaps 4000 gaps)) :
    (CurrentKernelDerivatives.cell4376Lower : ℝ) ≤
      CurrentKernelDerivatives.closedWeightD2 (realSpan gaps.1 0 1) := by
  apply Annotated.Tree.check_sound
    (problem := problem)
    (Conclusion := fun g : CurrentGapVector =>
      (CurrentKernelDerivatives.cell4376Lower : ℝ) ≤
        CurrentKernelDerivatives.closedWeightD2 (realSpan g.1 0 1))
    (locate := locateGaps 4000)
    (transfer := fun _ h => by
      change (1 : ℤ) ≤ 0 at h
      omega)
    demoTangentOK demoTangentOK_sound tree root
  · simp [tree, Annotated.Tree.check, demoTangentOK, evidence_checked]
  · exact hroot

end Demo

end Zeta23Ext.VerifiedCertificate.CurrentTangent

end
