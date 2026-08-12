/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.VerifiedCertificateArithmetic
import Zeta23Ext.CurrentKernelFormula

/-!
# Exact replay interface for the current weighted six-gap certificate

This module specializes the generic integer-tree checker to the exact pressure,
pair weights, grid geometry, and objective used by the production verifier.
Only the kernel-table inequalities and the (optional) tangent-leaf evidence
remain certificate-specific mathematical inputs.
-/

noncomputable section
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Zeta23Ext.VerifiedCertificate.CurrentReplay

open Zeta23Ext

/-! ## Cell spans and box spans -/

/-- Extend a six-vector of cell indices by zero. -/
def cellExt (point : Fin 6 → ℕ) (t : ℕ) : ℕ :=
  if h : t < 6 then point ⟨t, h⟩ else 0

/-- Cell-index sum for the gap interval `[i,i+r)`. -/
def cellSpan (point : Fin 6 → ℕ) (i r : ℕ) : ℕ :=
  ∑ t ∈ Finset.Ico i (i + r), cellExt point t

/-- Lower endpoint sum of a box over `[i,i+r)`. -/
def lowerSpan (box : Box 6) (i r : ℕ) : ℕ :=
  ∑ t ∈ Finset.Ico i (i + r), cellExt box.lo t

/-- Upper endpoint sum of a box over `[i,i+r)`. -/
def upperSpan (box : Box 6) (i r : ℕ) : ℕ :=
  ∑ t ∈ Finset.Ico i (i + r), cellExt box.hi t

lemma cellExt_between {box : Box 6} {point : Fin 6 → ℕ}
    (hpoint : box.Contains point) (t : ℕ) :
    cellExt box.lo t ≤ cellExt point t ∧ cellExt point t ≤ cellExt box.hi t := by
  unfold cellExt
  split
  · exact hpoint _
  · exact ⟨le_rfl, le_rfl⟩

lemma Box.lowerSpan_le_cellSpan {box : Box 6} {point : Fin 6 → ℕ}
    (hpoint : box.Contains point) (i r : ℕ) :
    lowerSpan box i r ≤ cellSpan point i r := by
  exact Finset.sum_le_sum fun t _ => (cellExt_between hpoint t).1

lemma Box.cellSpan_le_upperSpan {box : Box 6} {point : Fin 6 → ℕ}
    (hpoint : box.Contains point) (i r : ℕ) :
    cellSpan point i r ≤ upperSpan box i r := by
  exact Finset.sum_le_sum fun t _ => (cellExt_between hpoint t).2

/-! ## Exact range minima over a dyadic kernel table -/

/-- A dyadic table together with exact range-minimum replay data.

`rangeLower_le_value` and `rangeLower_mono` are finite integer properties of
the exported table, not transcendental assumptions.  `outside_zero` matches
the verifier's zero lower bound beyond the table cutoff.
-/
structure RangeKernelTable where
  table : DyadicKernelTable
  rangeLower : ℕ → ℕ → ℤ
  rangeLower_le_value : ∀ left right i (hi : i < table.cellCount),
    left ≤ i → i ≤ right → rangeLower left right ≤ table.value ⟨i, hi⟩
  rangeLower_mono : ∀ {outerLeft innerLeft innerRight outerRight},
    outerLeft ≤ innerLeft → innerRight ≤ outerRight →
      rangeLower outerLeft outerRight ≤ rangeLower innerLeft innerRight
  outside_zero : ∀ left right, table.cellCount ≤ right → rangeLower left right = 0

/-- A nonnegative real in a closed union of grid cells belongs to one of
those cells.  At the right endpoint we deliberately choose the final cell,
matching the closed-cell convention in `DyadicKernelTable.Sound`. -/
lemma exists_grid_cell {grid left right : ℕ} (hgrid : 0 < grid)
    (hle : left ≤ right)
    {x : ℝ} (hlower : (left : ℝ) / grid ≤ x)
    (hupper : x ≤ ((right : ℕ) + 1 : ℝ) / grid) :
    ∃ i : ℕ, left ≤ i ∧ i ≤ right ∧
      (i : ℝ) / grid ≤ x ∧ x ≤ ((i : ℕ) + 1 : ℝ) / grid := by
  have hx : 0 ≤ x := le_trans (by positivity : 0 ≤ (left : ℝ) / grid) hlower
  by_cases hend : x = ((right : ℕ) + 1 : ℝ) / grid
  · exact ⟨right, hle, le_rfl,
      by
        rw [hend]
        apply (div_le_div_iff_of_pos_right (by exact_mod_cast hgrid)).2
        exact_mod_cast (show right ≤ right + 1 by omega),
      hend.le⟩
  · let i := gridCell grid x
    have hiLower : left ≤ i := by
      apply Nat.le_floor
      have := (div_le_iff₀ (by exact_mod_cast hgrid : (0 : ℝ) < grid)).1 hlower
      simpa [i, gridCell, mul_comm] using this
    have hxlt : x < ((right : ℕ) + 1 : ℝ) / grid := lt_of_le_of_ne hupper hend
    have hiUpper : i ≤ right := by
      have hmul : (grid : ℝ) * x < (right : ℕ) + 1 := by
        have := (lt_div_iff₀ (by exact_mod_cast hgrid : (0 : ℝ) < grid)).1 hxlt
        simpa [mul_comm] using this
      have : i < right + 1 := by
        change ⌊(grid : ℝ) * x⌋₊ < right + 1
        rw [Nat.floor_lt (mul_nonneg (by positivity) hx)]
        exact_mod_cast hmul
      omega
    exact ⟨i, hiLower, hiUpper, gridCell_lower hgrid hx,
      (gridCell_upper hgrid x).le⟩

/-- Table soundness plus exact range-minimum replay bounds the true kernel
weight over the whole cell range. -/
theorem RangeKernelTable.rangeLower_sound (data : RangeKernelTable)
    (hsound : data.table.Sound CurrentWindow.weight)
    {left right : ℕ} {x : ℝ}
    (hle : left ≤ right)
    (hlower : (left : ℝ) / data.table.grid ≤ x)
    (hupper : x ≤ ((right : ℕ) + 1 : ℝ) / data.table.grid) :
    (data.rangeLower left right : ℝ) /
        (2 : ℝ) ^ data.table.scaleBits ≤ CurrentWindow.weight x := by
  rcases hsound with ⟨hgrid, hsound⟩
  by_cases hin : right < data.table.cellCount
  · obtain ⟨i, hli, hir, hcellLower, hcellUpper⟩ :=
      exists_grid_cell hgrid hle hlower hupper
    have hvalue := hsound ⟨i, lt_of_le_of_lt hir hin⟩ x hcellLower hcellUpper
    have hrange : (data.rangeLower left right : ℝ) ≤
        data.table.value ⟨i, lt_of_le_of_lt hir hin⟩ := by
      exact_mod_cast data.rangeLower_le_value left right i
        (lt_of_le_of_lt hir hin) hli hir
    exact le_trans ((div_le_div_iff_of_pos_right (by positivity)).2 hrange) hvalue
  · rw [data.outside_zero left right (by omega)]
    norm_num
    exact CurrentWindow.weight_nonneg x

/-! ## The exact scaled integer problem -/

/-- Common positive scale clearing the target, pressure, grid, pair-weight,
and dyadic-table denominators. -/
def scale (grid scaleBits : ℕ) : ℕ :=
  100000 * 2300 * grid * 1000000 * 2 ^ scaleBits

def target (grid scaleBits : ℕ) : ℤ :=
  509 * (2300 * grid * 1000000 * 2 ^ scaleBits)

def pressureCoefficient (scaleBits : ℕ) : ℤ :=
  100000 * 1000000 * 2 ^ scaleBits

def pairCoefficient (grid i j : ℕ) : ℤ :=
  100000 * 2300 * grid * Weighted.pairWeightNumerator i j

/-- Scaled lower score attached to a lattice cell vector. -/
def exactScore (data : RangeKernelTable) (point : Fin 6 → ℕ) : ℤ :=
  pressureCoefficient data.table.scaleBits * (pointSum point : ℤ) +
    ∑ r ∈ Finset.Icc (1 : ℕ) 6,
      ∑ i ∈ Finset.range (7 - r),
        pairCoefficient data.table.grid i (i + r) *
          data.rangeLower (cellSpan point i r) (cellSpan point i r + r - 1)

/-- Scaled lower score for an entire subdivision box. -/
def lowerScore (data : RangeKernelTable) (box : Box 6) : ℤ :=
  pressureCoefficient data.table.scaleBits * (box.sumLo : ℤ) +
    ∑ r ∈ Finset.Icc (1 : ℕ) 6,
      ∑ i ∈ Finset.range (7 - r),
        pairCoefficient data.table.grid i (i + r) *
          data.rangeLower (lowerSpan box i r) (upperSpan box i r + r - 1)

lemma pairCoefficient_nonneg (grid i j : ℕ) :
    0 ≤ pairCoefficient grid i j := by
  unfold pairCoefficient
  positivity

theorem lowerScore_sound (data : RangeKernelTable) :
    ∀ box point, box.Contains point →
      lowerScore data box ≤ exactScore data point := by
  intro box point hpoint
  unfold lowerScore exactScore
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast Box.sumLo_le_pointSum hpoint)
      (by unfold pressureCoefficient; positivity)
  · refine Finset.sum_le_sum fun r hr => ?_
    rw [Finset.mem_Icc] at hr
    refine Finset.sum_le_sum fun i hi => ?_
    apply mul_le_mul_of_nonneg_left _ (pairCoefficient_nonneg _ _ _)
    apply data.rangeLower_mono
    · exact Box.lowerSpan_le_cellSpan hpoint i r
    · have := Box.cellSpan_le_upperSpan hpoint i r
      omega

/-! ## Transfer from located cells to the exact real objective -/

/-- Real gap span occurring in `Weighted.F6`. -/
def realSpan (gaps : Fin 6 → ℝ) (i r : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico i (i + r), Aggregation.gext gaps t

/-- Canonical production-grid locator specialized to current gap vectors. -/
def locateGaps (grid : ℕ) (gaps : CurrentGapVector) : Fin 6 → ℕ :=
  fun i => gridCell grid (gaps.1 i)

lemma cellExt_locateOnGrid {grid : ℕ}
    (gaps : CurrentGapVector) {t : ℕ} (ht : t < 6) :
    cellExt (locateGaps grid gaps) t = gridCell grid (gaps.1 ⟨t, ht⟩) := by
  simp [cellExt, locateGaps, ht]

lemma gext_eq_gap {gaps : Fin 6 → ℝ} {t : ℕ} (ht : t < 6) :
    Aggregation.gext gaps t = gaps ⟨t, ht⟩ := by
  simp [Aggregation.gext, ht]

/-- Located cell sums bound the corresponding real gap span from below. -/
theorem cellSpan_lower {grid i r : ℕ} (hgrid : 0 < grid)
    (gaps : CurrentGapVector) (hir : i + r ≤ 6) :
    (cellSpan (locateGaps grid gaps) i r : ℝ) / grid ≤
      realSpan gaps.1 i r := by
  unfold cellSpan realSpan
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun t ht => ?_
  rw [Finset.mem_Ico] at ht
  rw [cellExt_locateOnGrid gaps (by omega), gext_eq_gap (by omega)]
  exact gridCell_lower hgrid (gaps.2 _)

/-- The real span is bounded above by the end of the last possible summed
cell.  Closed upper bounds match the table's closed-cell soundness format. -/
theorem cellSpan_upper {grid i r : ℕ} (hgrid : 0 < grid)
    (gaps : CurrentGapVector) (hir : i + r ≤ 6) :
    realSpan gaps.1 i r ≤
      ((cellSpan (locateGaps grid gaps) i r : ℕ) + r : ℝ) / grid := by
  unfold cellSpan realSpan
  calc
    ∑ t ∈ Finset.Ico i (i + r), Aggregation.gext gaps.1 t
        ≤ ∑ t ∈ Finset.Ico i (i + r),
            ((cellExt (locateGaps grid gaps) t : ℕ) + 1 : ℝ) / grid := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [Finset.mem_Ico] at ht
          rw [cellExt_locateOnGrid gaps (by omega), gext_eq_gap (by omega)]
          exact (gridCell_upper hgrid _).le
    _ = ((∑ t ∈ Finset.Ico i (i + r),
            cellExt (locateGaps grid gaps) t : ℕ) + r : ℝ) / grid := by
          rw [← Finset.sum_div]
          push_cast
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
          have : i + r - i = r := by omega
          rw [this]

/-- Located coordinates bound the pressure sum from below. -/
theorem pointSum_lower {grid : ℕ} (hgrid : 0 < grid)
    (gaps : CurrentGapVector) :
    (pointSum (locateGaps grid gaps) : ℝ) / grid ≤ ∑ i, gaps.1 i := by
  unfold pointSum
  rw [Nat.cast_sum, Finset.sum_div]
  exact Finset.sum_le_sum fun i _ => gridCell_lower hgrid (gaps.2 i)

lemma scale_pos {grid scaleBits : ℕ} (hgrid : 0 < grid) :
    (0 : ℝ) < scale grid scaleBits := by
  unfold scale
  positivity

/-- The scaled integer target is exactly the paper's rational target. -/
theorem target_div_scale {grid scaleBits : ℕ} (hgrid : 0 < grid) :
    (target grid scaleBits : ℝ) / scale grid scaleBits = Weighted.beta := by
  unfold target scale Weighted.beta
  push_cast
  field_simp
  norm_num

/-- The integer pressure term has exactly the real normalization used by
`Weighted.F6`. -/
theorem pressureTerm_div_scale {grid scaleBits value : ℕ} (hgrid : 0 < grid) :
    ((pressureCoefficient scaleBits * (value : ℤ) : ℤ) : ℝ) /
        scale grid scaleBits = Weighted.pressure * ((value : ℝ) / grid) := by
  unfold pressureCoefficient scale Weighted.pressure
  push_cast
  field_simp
  ring

/-- Each scaled integer pair term has exactly the real pair-weight and dyadic
normalization used by the verifier. -/
theorem pairTerm_div_scale {grid scaleBits i j : ℕ} (hgrid : 0 < grid)
    (value : ℤ) :
    ((pairCoefficient grid i j * value : ℤ) : ℝ) / scale grid scaleBits =
      Weighted.pairWeight i j * ((value : ℝ) / (2 : ℝ) ^ scaleBits) := by
  unfold pairCoefficient scale Weighted.pairWeight
  push_cast
  field_simp

/-- The located lattice score is a genuine scaled lower bound for the exact
current weighted objective.  The only analytic premise is table soundness. -/
theorem exactScore_div_scale_le (data : RangeKernelTable)
    (hsound : data.table.Sound CurrentWindow.weight)
    (gaps : CurrentGapVector) :
    (exactScore data (locateGaps data.table.grid gaps) : ℝ) /
        scale data.table.grid data.table.scaleBits ≤
      Weighted.F6 CurrentWindow.weight gaps.1 := by
  rcases hsound with ⟨hgrid, htable⟩
  have hsound' : data.table.Sound CurrentWindow.weight := ⟨hgrid, htable⟩
  unfold exactScore Weighted.F6 Weighted.F6With
  rw [Int.cast_add, add_div]
  apply add_le_add
  · rw [pressureTerm_div_scale hgrid]
    exact mul_le_mul_of_nonneg_left (pointSum_lower hgrid gaps) Weighted.pressure_nonneg
  · rw [Int.cast_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun r hr => ?_
    rw [Finset.mem_Icc] at hr
    rw [Int.cast_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun i hi => ?_
    have hir : i + r ≤ 6 := by
      rw [Finset.mem_range] at hi
      have := Nat.lt_sub_iff_add_lt.mp hi
      omega
    rw [pairTerm_div_scale hgrid]
    apply mul_le_mul_of_nonneg_left _ (Weighted.pairWeight_nonneg _ _)
    apply data.rangeLower_sound hsound'
    · omega
    · exact cellSpan_lower hgrid gaps hir
    · have hu := cellSpan_upper hgrid gaps hir
      change realSpan gaps.1 i r ≤
        (((cellSpan (locateGaps data.table.grid gaps) i r + r - 1 : ℕ) : ℝ) + 1) /
          data.table.grid
      calc
        realSpan gaps.1 i r ≤
            ((cellSpan (locateGaps data.table.grid gaps) i r : ℕ) + r : ℝ) /
              data.table.grid := hu
        _ = (((cellSpan (locateGaps data.table.grid gaps) i r + r - 1 : ℕ) : ℝ) + 1) /
              data.table.grid := by
            congr 1
            norm_cast
            omega

/-- Integer acceptance transfers to the exact current local inequality. -/
theorem target_le_exactScore_implies_local (data : RangeKernelTable)
    (hsound : data.table.Sound CurrentWindow.weight)
    (gaps : CurrentGapVector)
    (hscore : target data.table.grid data.table.scaleBits ≤
      exactScore data (locateGaps data.table.grid gaps)) :
    Weighted.beta ≤ Weighted.F6 CurrentWindow.weight gaps.1 := by
  have hgrid := hsound.1
  rw [show Weighted.beta = (target data.table.grid data.table.scaleBits : ℝ) /
      scale data.table.grid data.table.scaleBits by
        symm; exact target_div_scale hgrid]
  exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hscore)
    (le_of_lt (scale_pos hgrid))) (exactScore_div_scale_le data hsound gaps)

/-- The actual `IntegerLowerBoundProblem` consumed by forest replay. -/
def problem (data : RangeKernelTable) : IntegerLowerBoundProblem 6 where
  target := target data.table.grid data.table.scaleBits
  exactScore := exactScore data
  lowerScore := lowerScore data
  lowerScore_sound := lowerScore_sound data

/-! ## Initialization pruning and construction of the real bridge -/

/-- The exact pressure cutoff recorded by the production verifier. -/
def pressureCutoff : ℕ := 46830

/-- At grid 4000, the recorded cutoff is safely beyond the exact pressure-only
threshold (which is 46828 cells). -/
theorem target_le_pressure_at_cutoff (scaleBits : ℕ) :
    target 4000 scaleBits ≤ pressureCoefficient scaleBits * pressureCutoff := by
  unfold target pressureCoefficient pressureCutoff
  have hp : (0 : ℤ) ≤ (2 : ℤ) ^ scaleBits := by positivity
  push_cast
  ring_nf
  nlinarith

/-- The pressure term alone is a lower bound for the whole current objective. -/
theorem pressure_le_F6 (gaps : CurrentGapVector) :
    Weighted.pressure * (∑ i, gaps.1 i) ≤
      Weighted.F6 CurrentWindow.weight gaps.1 := by
  unfold Weighted.F6 Weighted.F6With
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun i _ =>
    mul_nonneg (Weighted.pairWeight_nonneg _ _) (CurrentWindow.weight_nonneg _)

/-- A located cell vector past the production cutoff is discharged by pressure
alone, with no kernel-table premise. -/
theorem pressure_cutoff_local (scaleBits : ℕ) (gaps : CurrentGapVector)
    (hcutoff : pressureCutoff ≤ pointSum (locateGaps 4000 gaps)) :
    Weighted.beta ≤ Weighted.F6 CurrentWindow.weight gaps.1 := by
  have hscore : target 4000 scaleBits ≤
      pressureCoefficient scaleBits * (pointSum (locateGaps 4000 gaps) : ℤ) := by
    exact le_trans (target_le_pressure_at_cutoff scaleBits)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hcutoff)
        (by unfold pressureCoefficient; positivity))
  rw [show Weighted.beta = (target 4000 scaleBits : ℝ) / scale 4000 scaleBits by
      symm; exact target_div_scale (by norm_num)]
  calc
    (target 4000 scaleBits : ℝ) / scale 4000 scaleBits
        ≤ ((pressureCoefficient scaleBits *
            (pointSum (locateGaps 4000 gaps) : ℤ) : ℤ) : ℝ) /
              scale 4000 scaleBits :=
          div_le_div_of_nonneg_right (by exact_mod_cast hscore) (by positivity)
    _ = Weighted.pressure *
          ((pointSum (locateGaps 4000 gaps) : ℝ) / 4000) :=
          pressureTerm_div_scale (by norm_num)
    _ ≤ Weighted.pressure * (∑ i, gaps.1 i) :=
          mul_le_mul_of_nonneg_left (pointSum_lower (by norm_num) gaps)
            Weighted.pressure_nonneg
    _ ≤ Weighted.F6 CurrentWindow.weight gaps.1 := pressure_le_F6 gaps

/-- Finite structural evidence exported with the 324 initial root boxes.

For every lattice vector below the pressure cutoff, the evidence says either
that it belongs to a replayed root, or that initialization's one-body pruning
already establishes the *same scaled lattice score* used by the real-transfer
theorem.  This is a finite integer property of the root-box/table artifact.
-/
structure InitialRootEvidence (data : RangeKernelTable) (roots : List (Box 6)) where
  root_count : roots.length = productionRootCount
  classify : ∀ point : Fin 6 → ℕ,
    pressureCutoff ≤ pointSum point ∨ Forest.Covers roots point ∨
      target data.table.grid data.table.scaleBits ≤ exactScore data point

/-- The exact forest bridge derived from table soundness and initialization
classification.  No opaque real-score transfer field remains. -/
def currentForestBridge (data : RangeKernelTable) (roots : List (Box 6))
    (hgrid : data.table.grid = 4000)
    (hsound : data.table.Sound CurrentWindow.weight)
    (initial : InitialRootEvidence data roots) :
    ForestRealBridge (problem data) roots CurrentGapVector fun g =>
      Weighted.beta ≤ Weighted.F6 CurrentWindow.weight g.1 where
  locate := locateGaps data.table.grid
  classify := fun gaps => by
    rcases initial.classify (locateGaps data.table.grid gaps) with hpressure | hrest
    · left
      have hpressure' : pressureCutoff ≤ pointSum (locateGaps 4000 gaps) := by
        simpa [hgrid] using hpressure
      exact pressure_cutoff_local data.table.scaleBits gaps hpressure'
    · rcases hrest with hcovered | hscore
      · exact Or.inr hcovered
      · left
        exact target_le_exactScore_implies_local data hsound gaps hscore
  transfer := fun gaps hscore =>
    target_le_exactScore_implies_local data hsound gaps hscore

/-- A checked production forest, exact initialization evidence, and a sound
dyadic kernel table discharge the current local certificate. -/
theorem currentLocalCertificate_of_replay
    (data : RangeKernelTable) (roots : List (Box 6))
    (hgrid : data.table.grid = 4000)
    (hsound : data.table.Sound CurrentWindow.weight)
    (initial : InitialRootEvidence data roots)
    (trees : List (Tree 6))
    (hcheck : Forest.check (problem data).leafOK trees roots = true) :
    CurrentWindow.LocalCertificate :=
  currentLocalCertificate_of_checked_forest (problem data) roots trees
    (currentForestBridge data roots hgrid hsound initial) hcheck

end Zeta23Ext.VerifiedCertificate.CurrentReplay
