/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWeightD2CellChecker
import Zeta23Ext.CurrentCertificateReplay

/-!
# Shared curvature cells and sparse range-minimum evidence

Production tangent leaves reuse the same current-kernel cells billions of
times.  This module separates the expensive semantic cells from compact leaf
queries.  A cell is checked once in a contiguous global table.  A rectangular
sparse table is then checked once from its level-zero cell bounds and its
two-child recurrence.  One leaf range carries two overlapping power-of-two
blocks, so its executable check is constant-size.

No theorem-valued fields occur in either table: all soundness is derived from
Boolean acceptance and the genuine `CurrentWeightD2CellChecker.CellWitness`
theorem.
-/

noncomputable section

open Set

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.CurvatureRMQ

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay

abbrev SemanticCell := CurrentWeightD2CellChecker.CellWitness

/-- One contiguous, globally shared table of semantic current-curvature
cells. -/
structure CellTable where
  first : ℕ
  count : ℕ
  cells : Fin count → SemanticCell

noncomputable def CellTable.check (t : CellTable) : Bool := by
  classical
  exact decide (∀ i, (t.cells i).check = true ∧
    (t.cells i).cell = t.first + i.val)

private lemma cellTable_check_facts {t : CellTable} (h : t.check = true) :
    ∀ i, (t.cells i).check = true ∧
      (t.cells i).cell = t.first + i.val := by
  classical
  simpa [CellTable.check] using of_decide_eq_true h

/-- Semantic meaning of a checked global row. -/
theorem CellTable.cell_sound (t : CellTable) (hcheck : t.check = true)
    (i : Fin t.count) {x : ℝ}
    (hx : x ∈ Icc (((t.first + i.val : ℕ) : ℝ) / 4000)
      (((t.first + i.val + 1 : ℕ) : ℝ) / 4000)) :
    ((t.cells i).lower : ℝ) ≤
      CurrentKernelTotalDerivatives.closedWeightD2Total x := by
  have hf := cellTable_check_facts hcheck i
  rw [← hf.2] at hx
  exact (t.cells i).sound hf.1 hx

/-- Globally shared power-of-two range-minimum table.  Unused entries in the
rectangular array are harmless; `check` constrains every geometrically valid
entry. -/
structure SparseTable where
  cells : CellTable
  depth : ℕ
  /-- Rectangular storage. Only entries whose blocks fit in `cells` are used
  or constrained by `check`. -/
  lower : ℕ → ℕ → ℚ

noncomputable def SparseTable.check (t : SparseTable) : Bool := by
  classical
  exact t.cells.check && decide
    (t.depth ≤ 64 ∧
      2 ^ t.depth ≤ 2 * max 1 t.cells.count ∧
      (∀ i : Fin t.cells.count, t.lower 0 i.val ≤ (t.cells.cells i).lower) ∧
      ∀ (p : Fin t.depth) (start : Fin t.cells.count),
        start.val + 2 ^ (p.val + 1) ≤ t.cells.count →
          t.lower (p.val + 1) start.val ≤ t.lower p.val start.val ∧
          t.lower (p.val + 1) start.val ≤
            t.lower p.val (start.val + 2 ^ p.val))

private lemma sparse_check_facts {t : SparseTable} (h : t.check = true) :
    t.cells.check = true ∧
    (∀ i : Fin t.cells.count, t.lower 0 i.val ≤ (t.cells.cells i).lower) ∧
      ∀ (p : Fin t.depth) (start : Fin t.cells.count),
        start.val + 2 ^ (p.val + 1) ≤ t.cells.count →
          t.lower (p.val + 1) start.val ≤ t.lower p.val start.val ∧
          t.lower (p.val + 1) start.val ≤
            t.lower p.val (start.val + 2 ^ p.val) := by
  rw [SparseTable.check, Bool.and_eq_true] at h
  exact ⟨h.1, (of_decide_eq_true h.2).2.2⟩

/-- Executable resource bound carried by every accepted sparse table. -/
theorem SparseTable.depth_le (t : SparseTable) (h : t.check = true) :
    t.depth ≤ 64 := by
  rw [SparseTable.check, Bool.and_eq_true] at h
  exact (of_decide_eq_true h.2).1

/-- An accepted table cannot advertise exponentially more levels than its
semantic cell count needs. -/
theorem SparseTable.pow_depth_le (t : SparseTable) (h : t.check = true) :
    2 ^ t.depth ≤ 2 * max 1 t.cells.count := by
  rw [SparseTable.check, Bool.and_eq_true] at h
  exact (of_decide_eq_true h.2).2.1

/-- A compact reference to one valid power-of-two block. -/
structure BlockRef where
  level : ℕ
  start : ℕ
  deriving DecidableEq

def BlockRef.width (b : BlockRef) : ℕ := 2 ^ b.level
def BlockRef.finish (b : BlockRef) : ℕ := b.start + b.width

def BlockRef.Valid (t : SparseTable) (b : BlockRef) : Prop :=
  b.level ≤ t.depth ∧ b.finish ≤ t.cells.count

noncomputable def BlockRef.check (t : SparseTable) (b : BlockRef) : Bool := by
  classical
  exact decide (b.Valid t)

def SparseTable.blockLower (t : SparseTable) (b : BlockRef) : ℚ :=
  t.lower b.level b.start

def CellTable.cellLower (t : CellTable) (cell : ℕ) : ℚ :=
  if h : cell < t.count then (t.cells ⟨cell, h⟩).lower else 0

private theorem SparseTable.blockLower_le_cell_aux (t : SparseTable)
    (hcheck : t.check = true) : ∀ (level : ℕ), level ≤ t.depth →
    ∀ (start cell : ℕ), start + 2 ^ level ≤ t.cells.count →
      start ≤ cell → cell < start + 2 ^ level →
      t.blockLower ⟨level, start⟩ ≤ t.cells.cellLower cell := by
  intro level
  induction level with
  | zero =>
      intro _ start cell hvalid hlo hhi
      have hcell : cell = start := by norm_num at hhi; omega
      subst cell
      simp only [SparseTable.blockLower]
      rw [CellTable.cellLower, dif_pos (by omega)]
      exact (sparse_check_facts hcheck).2.1 _
  | succ level ih =>
      intro hlevel start cell hvalid hlo hhi
      have hdepth : level < t.depth := by omega
      let p : Fin t.depth := ⟨level, hdepth⟩
      have hstart : start < t.cells.count := by
        have : 0 < 2 ^ (level + 1) := by positivity
        omega
      let s : Fin t.cells.count := ⟨start, hstart⟩
      have hpow : 2 ^ (level + 1) = 2 ^ level + 2 ^ level := by
        rw [pow_succ]
        ring
      have hleftValid : start + 2 ^ level ≤ t.cells.count := by
        rw [hpow] at hvalid
        omega
      have hrightValid : start + 2 ^ level + 2 ^ level ≤ t.cells.count := by
        omega
      have hrec := (sparse_check_facts hcheck).2.2 p s (by
        simpa [p, s] using hvalid)
      simp only [SparseTable.blockLower]
      by_cases hside : cell < start + 2 ^ level
      · have hlower : t.lower (level + 1) start ≤
            t.blockLower ⟨level, start⟩ := by
          simp only [SparseTable.blockLower]
          exact hrec.1
        exact hlower.trans (ih (by omega) start cell hleftValid hlo hside)
      · have hlower : t.lower (level + 1) start ≤
            t.blockLower ⟨level, start + 2 ^ level⟩ := by
          simp only [SparseTable.blockLower]
          exact hrec.2
        exact hlower.trans (ih (by omega) (start + 2 ^ level) cell hrightValid
          (by omega) (by
            rw [hpow] at hhi
            omega))

/-- Every checked sparse block is a genuine lower bound for every semantic
cell it covers. -/
theorem SparseTable.blockLower_le_cell (t : SparseTable)
    (hcheck : t.check = true) (b : BlockRef) (hb : b.Valid t)
    (cell : ℕ) (hlo : b.start ≤ cell) (hhi : cell < b.finish) :
    t.blockLower b ≤ t.cells.cellLower cell := by
  exact t.blockLower_le_cell_aux hcheck b.level hb.1 b.start cell
    (by simpa [BlockRef.finish, BlockRef.width] using hb.2) hlo
    (by simpa [BlockRef.finish, BlockRef.width] using hhi)

/-- Constant-size range-minimum witness.  The two blocks start and end at the
query endpoints and overlap or touch, hence cover the whole inclusive range. -/
structure RangeWitness where
  left : ℕ
  right : ℕ
  lower : ℚ
  leftBlock : BlockRef
  rightBlock : BlockRef
  deriving DecidableEq

noncomputable def RangeWitness.check (t : SparseTable) (r : RangeWitness) : Bool := by
  classical
  exact decide (r.left ≤ r.right ∧ r.right < t.cells.count ∧
    r.leftBlock.Valid t ∧ r.rightBlock.Valid t ∧
    r.leftBlock.start = r.left ∧ r.rightBlock.finish = r.right + 1 ∧
    r.rightBlock.start ≤ r.leftBlock.finish ∧
    r.lower ≤ t.blockLower r.leftBlock ∧
    r.lower ≤ t.blockLower r.rightBlock)

private lemma range_check_facts {t : SparseTable} {r : RangeWitness}
    (h : r.check t = true) :
    r.left ≤ r.right ∧ r.right < t.cells.count ∧
    r.leftBlock.Valid t ∧ r.rightBlock.Valid t ∧
    r.leftBlock.start = r.left ∧ r.rightBlock.finish = r.right + 1 ∧
    r.rightBlock.start ≤ r.leftBlock.finish ∧
    r.lower ≤ t.blockLower r.leftBlock ∧
    r.lower ≤ t.blockLower r.rightBlock := by
  classical
  simpa [RangeWitness.check] using of_decide_eq_true h

private theorem RangeWitness.lower_le_cell {t : SparseTable} {r : RangeWitness}
    (htable : t.check = true) (hrange : r.check t = true)
    (cell : ℕ) (hlo : r.left ≤ cell) (hhi : cell ≤ r.right) :
    r.lower ≤ t.cells.cellLower cell := by
  have hf := range_check_facts hrange
  by_cases hleft : cell < r.leftBlock.finish
  · exact hf.2.2.2.2.2.2.2.1.trans
      (t.blockLower_le_cell htable r.leftBlock hf.2.2.1 cell
        (by omega) hleft)
  · exact hf.2.2.2.2.2.2.2.2.trans
      (t.blockLower_le_cell htable r.rightBlock hf.2.2.2.1 cell
        (by omega) (by omega))

/-- A compact accepted query proves the common lower bound over the whole
closed union of global current-grid cells. -/
theorem RangeWitness.sound (t : SparseTable) (r : RangeWitness)
    (htable : t.check = true) (hrange : r.check t = true) {x : ℝ}
    (hx : x ∈ Icc (((t.cells.first + r.left : ℕ) : ℝ) / 4000)
      (((t.cells.first + r.right + 1 : ℕ) : ℝ) / 4000)) :
    (r.lower : ℝ) ≤ CurrentKernelTotalDerivatives.closedWeightD2Total x := by
  have hf := range_check_facts hrange
  obtain ⟨cell, hcellLo, hcellHi, hxLo, hxHi⟩ := exists_grid_cell
    (grid := 4000) (by norm_num) (Nat.add_le_add_left hf.1 t.cells.first) hx.1 (by
      norm_num at hx ⊢
      exact hx.2)
  have hlocal : t.cells.first ≤ cell := by omega
  let k : Fin t.cells.count := ⟨cell - t.cells.first, by omega⟩
  have hkLo : r.left ≤ k.val := by dsimp [k]; omega
  have hkHi : k.val ≤ r.right := by dsimp [k]; omega
  have hlower : (r.lower : ℝ) ≤ ((t.cells.cells k).lower : ℝ) := by
    have hk := r.lower_le_cell htable hrange k.val hkLo hkHi
    rw [CellTable.cellLower, dif_pos k.isLt] at hk
    exact_mod_cast hk
  apply hlower.trans
  apply t.cells.cell_sound (sparse_check_facts htable).1 k
  dsimp [k]
  have hcellEq : t.cells.first + (cell - t.cells.first) = cell := by omega
  rw [hcellEq]
  constructor
  · exact hxLo
  · norm_num at hxHi ⊢
    exact hxHi

end Zeta23Ext.VerifiedCertificate.CurrentTangent.CurvatureRMQ

end
