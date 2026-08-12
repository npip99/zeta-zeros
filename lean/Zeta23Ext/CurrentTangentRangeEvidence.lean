/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentEvidence

/-!
# Wide-range evidence for production tangent leaves

Production tangent boxes cross many kernel cells.  This module supersedes the
single-cell `SpanEvidence` format with two independently checked components:

* `SpanRange` proves exact box geometry for the whole real span; and
* `KernelRangeWitness` supplies a semantic witness for every consecutive
  kernel cell in that inclusive range, with one common rational lower bound.

The format cannot accept an undercovered wide box.  It also keeps table data
semantic: every registered cell constructor carries a theorem about the true
current-window second derivative.
-/

noncomputable section

open Set

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.Range

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay

/-- Registered semantic second-derivative cells.  The finite generator must
extend this type (or an equivalent generated table) before wide production
ranges can pass. -/
inductive CellWitness where
  | cell4376
  deriving DecidableEq

def CellWitness.cell : CellWitness → ℕ
  | .cell4376 => 4376

def CellWitness.lower : CellWitness → ℚ
  | .cell4376 => CurrentKernelDerivatives.cell4376Lower

theorem CellWitness.sound (w : CellWitness) {x : ℝ}
    (hx : x ∈ Icc ((w.cell : ℝ) / 4000) ((w.cell + 1 : ℕ) / 4000)) :
    (w.lower : ℝ) ≤ CurrentKernelDerivatives.closedWeightD2 x := by
  cases w
  exact ProductionCell4376Jets.cell4376_semantic hx

/-- Exact geometry of one consecutive-gap span over a leaf box.  `left` and
`right` are inclusive kernel-cell indices. -/
structure SpanRange where
  start : ℕ
  span : ℕ
  left : ℕ
  right : ℕ
  deriving DecidableEq

def SpanRange.check (r : SpanRange) (box : Box 6) : Bool :=
  decide (0 < r.span ∧ r.start + r.span ≤ 6 ∧ r.left ≤ r.right ∧
    r.left ≤ lowerSpan box r.start r.span ∧
    upperSpan box r.start r.span + r.span ≤ r.right + 1)

private lemma spanRange_check_facts {r : SpanRange} {box : Box 6}
    (h : r.check box = true) :
    0 < r.span ∧ r.start + r.span ≤ 6 ∧ r.left ≤ r.right ∧
      r.left ≤ lowerSpan box r.start r.span ∧
      upperSpan box r.start r.span + r.span ≤ r.right + 1 := by
  simpa [SpanRange.check] using of_decide_eq_true h

theorem SpanRange.realSpan_mem (r : SpanRange) (box : Box 6)
    (hcheck : r.check box = true) (gaps : CurrentGapVector)
    (hbox : box.Contains (locateGaps 4000 gaps)) :
    realSpan gaps.1 r.start r.span ∈
      Icc ((r.left : ℝ) / 4000) ((r.right + 1 : ℕ) / 4000) := by
  obtain ⟨_, hvalid, _, hlo, hhi⟩ := spanRange_check_facts hcheck
  have hcellLo := Box.lowerSpan_le_cellSpan hbox r.start r.span
  have hcellHi := Box.cellSpan_le_upperSpan hbox r.start r.span
  have hrealLo := cellSpan_lower (grid := 4000) (by norm_num) gaps hvalid
  have hrealHi := cellSpan_upper (grid := 4000) (by norm_num) gaps hvalid
  constructor
  · have hnat : r.left ≤ cellSpan (locateGaps 4000 gaps) r.start r.span :=
      hlo.trans hcellLo
    have hcast : (r.left : ℝ) ≤
        cellSpan (locateGaps 4000 gaps) r.start r.span := by exact_mod_cast hnat
    exact le_trans (div_le_div_of_nonneg_right hcast (by norm_num)) hrealLo
  · have hnat : cellSpan (locateGaps 4000 gaps) r.start r.span + r.span ≤
        r.right + 1 := by omega
    have hcast :
        ((cellSpan (locateGaps 4000 gaps) r.start r.span : ℕ) + r.span : ℝ) ≤
          (r.right + 1 : ℕ) := by exact_mod_cast hnat
    exact hrealHi.trans (div_le_div_of_nonneg_right hcast (by norm_num))

/-- Common lower bound plus one registered semantic witness per consecutive
cell.  The vector length is exactly the inclusive range cardinality. -/
structure KernelRangeWitness where
  left : ℕ
  right : ℕ
  lower : ℚ
  witnesses : Fin (right + 1 - left) → CellWitness
  deriving DecidableEq

noncomputable def KernelRangeWitness.check (r : KernelRangeWitness) : Bool := by
  classical
  exact decide (r.left ≤ r.right ∧ ∀ k,
    (r.witnesses k).cell = r.left + k ∧ r.lower ≤ (r.witnesses k).lower)

private lemma kernelRange_check_facts {r : KernelRangeWitness}
    (h : r.check = true) : r.left ≤ r.right ∧ ∀ k,
      (r.witnesses k).cell = r.left + k ∧
        r.lower ≤ (r.witnesses k).lower := by
  classical
  simpa [KernelRangeWitness.check] using of_decide_eq_true h

theorem KernelRangeWitness.sound (r : KernelRangeWitness)
    (hcheck : r.check = true) {x : ℝ}
    (hx : x ∈ Icc ((r.left : ℝ) / 4000) ((r.right + 1 : ℕ) / 4000)) :
    (r.lower : ℝ) ≤ CurrentKernelDerivatives.closedWeightD2 x := by
  have hf := kernelRange_check_facts hcheck
  have hxUpper : x ≤ ((r.right : ℝ) + 1) / 4000 := by
    norm_num at hx ⊢
    exact hx.2
  obtain ⟨i, hli, hir, hxiLo, hxiHi⟩ := exists_grid_cell
    (grid := 4000) (by norm_num) hf.1 hx.1 hxUpper
  let k : Fin (r.right + 1 - r.left) := ⟨i - r.left, by omega⟩
  have hk := hf.2 k
  have hcell : (r.witnesses k).cell = i := by
    rw [hk.1]
    dsimp [k]
    omega
  have hcellMem : x ∈ Icc (((r.witnesses k).cell : ℝ) / 4000)
      (((r.witnesses k).cell + 1 : ℕ) / 4000) := by
    rw [hcell]
    constructor
    · exact hxiLo
    · norm_num at hxiHi ⊢
      exact hxiHi
  have hlower : (r.lower : ℝ) ≤ ((r.witnesses k).lower : ℝ) := by
    exact_mod_cast hk.2
  exact hlower.trans ((r.witnesses k).sound hcellMem)

/-- Full evidence for one Hessian span. -/
structure Evidence where
  geometry : SpanRange
  range : KernelRangeWitness
  deriving DecidableEq

noncomputable def Evidence.check (e : Evidence) (box : Box 6) : Bool :=
  e.geometry.check box && e.range.check &&
    decide (e.geometry.left = e.range.left ∧ e.geometry.right = e.range.right)

private lemma evidence_check_facts {e : Evidence} {box : Box 6}
    (h : e.check box = true) :
    e.geometry.check box = true ∧ e.range.check = true ∧
      e.geometry.left = e.range.left ∧ e.geometry.right = e.range.right := by
  rw [Evidence.check, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, of_decide_eq_true h.2⟩

theorem Evidence.secondDerivative_sound (e : Evidence) (box : Box 6)
    (hcheck : e.check box = true) (gaps : CurrentGapVector)
    (hbox : box.Contains (locateGaps 4000 gaps)) :
    (e.range.lower : ℝ) ≤ CurrentKernelDerivatives.closedWeightD2
      (realSpan gaps.1 e.geometry.start e.geometry.span) := by
  have hf := evidence_check_facts hcheck
  have hmem := e.geometry.realSpan_mem box hf.1 gaps hbox
  rw [hf.2.2.1, hf.2.2.2] at hmem
  exact e.range.sound hf.2.1 hmem

/-! ## Regressions -/

namespace Demo

def cell4376Range : KernelRangeWitness where
  left := 4376
  right := 4376
  lower := CurrentKernelDerivatives.cell4376Lower
  witnesses := fun _ => .cell4376

def narrow : Evidence where
  geometry := ⟨0, 1, 4376, 4376⟩
  range := cell4376Range

def narrowRoot : Box 6 where
  lo i := if i = 0 then 4376 else 0
  hi i := if i = 0 then 4376 else 0

theorem narrow_checked : narrow.check narrowRoot = true := by
  norm_num [Evidence.check, narrow, cell4376Range, KernelRangeWitness.check,
    SpanRange.check, narrowRoot, lowerSpan, upperSpan, cellExt,
    Finset.sum_Ico_eq_sub]
  intro k
  fin_cases k
  norm_num [CellWitness.cell, CellWitness.lower]

/-- First real production trace box.  Its first gap crosses 175 cells. -/
def wideRoot : Box 6 where
  lo := ![4376, 3784, 4049, 3783, 4315, 4027]
  hi := ![4550, 4049, 4314, 4048, 4579, 4201]

def wideFirstGap : SpanRange := ⟨0, 1, 4376, 4550⟩

theorem wideFirstGap_checked : wideFirstGap.check wideRoot = true := by
  norm_num [SpanRange.check, wideFirstGap, wideRoot, lowerSpan, upperSpan,
    cellExt, Finset.sum_Ico_eq_sub]

/-- A one-cell semantic table cannot cover the production-width geometry. -/
def undercoveredWide : Evidence where
  geometry := wideFirstGap
  range := cell4376Range

theorem undercoveredWide_rejected : undercoveredWide.check wideRoot = false := by
  norm_num [Evidence.check, undercoveredWide, wideFirstGap, cell4376Range,
    KernelRangeWitness.check, CellWitness.cell, CellWitness.lower]

end Demo

end Zeta23Ext.VerifiedCertificate.CurrentTangent.Range

end
