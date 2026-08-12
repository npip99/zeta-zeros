/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.VerifiedCertificateRoots
import Zeta23Ext.CurrentCertificateReplay

/-!
# Exact initial-root layout for the production certificate

The production search first keeps the connected components of the one-body
survivor set in each coordinate, then starts one root at every element of the
six-fold Cartesian product.  This module records that small, exact structural
artifact independently of the million-node subdivision forest.

The endpoint lists below are copied from the production root artifact.  A
decoded `Z23ROOT1` blob is connected to this definition only after an
executable equality check succeeds; the theorem does not trust JSON ordering
or an external root-count assertion.
-/

namespace Zeta23Ext.VerifiedCertificate.CurrentInitialRoots

open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay
set_option maxRecDepth 100000

abbrev CellRange := ℕ × ℕ

def ranges0 : List CellRange := [(3677, 5073), (6869, 45742)]
def ranges1 : List CellRange := [(3784, 4844), (7171, 9845), (10114, 45395)]
def ranges2 : List CellRange := [(3783, 4846), (7168, 9878), (10080, 45398)]
def ranges3 : List CellRange := ranges2
def ranges4 : List CellRange := ranges1
def ranges5 : List CellRange := ranges0

/-- Inclusive containment in a cell-index range. -/
def CellRange.Contains (range : CellRange) (cell : ℕ) : Prop :=
  range.1 ≤ cell ∧ cell ≤ range.2

def CellRange.containsBool (range : CellRange) (cell : ℕ) : Bool :=
  decide (range.1 ≤ cell ∧ cell ≤ range.2)

/-- The exact lexicographically ordered Cartesian product used by Python's
`itertools.product`. -/
def roots : List (Box 6) :=
  ranges0.flatMap fun c0 =>
  ranges1.flatMap fun c1 =>
  ranges2.flatMap fun c2 =>
  ranges3.flatMap fun c3 =>
  ranges4.flatMap fun c4 =>
  ranges5.map fun c5 =>
    ⟨![c0.1, c1.1, c2.1, c3.1, c4.1, c5.1],
      ![c0.2, c1.2, c2.2, c3.2, c4.2, c5.2]⟩

/-- The explicit Cartesian product has exactly the production root count. -/
theorem roots_length : roots.length = productionRootCount := by
  rfl

/-- Executable coordinate-specific component membership. -/
def coordinateCoveredBool (i : Fin 6) (cell : ℕ) : Bool :=
  match i.1 with
  | 0 => ranges0.any fun range => range.containsBool cell
  | 1 => ranges1.any fun range => range.containsBool cell
  | 2 => ranges2.any fun range => range.containsBool cell
  | 3 => ranges3.any fun range => range.containsBool cell
  | 4 => ranges4.any fun range => range.containsBool cell
  | _ => ranges5.any fun range => range.containsBool cell

/-- Propositional meaning of the executable component test. -/
def coordinateCovered (i : Fin 6) (cell : ℕ) : Prop :=
  coordinateCoveredBool i cell = true

/-- A point whose coordinates all survive one-body component pruning belongs
to one of the 324 explicitly reconstructed roots. -/
theorem covers_roots {point : Fin 6 → ℕ}
    (hcovered : ∀ i, coordinateCovered i (point i)) :
    Forest.Covers roots point := by
  have h0 := hcovered (0 : Fin 6)
  have h1 := hcovered (1 : Fin 6)
  have h2 := hcovered (2 : Fin 6)
  have h3 := hcovered (3 : Fin 6)
  have h4 := hcovered (4 : Fin 6)
  have h5 := hcovered (5 : Fin 6)
  simp [coordinateCovered, coordinateCoveredBool, CellRange.containsBool,
    List.any_eq_true] at h0 h1 h2 h3 h4 h5
  rcases h0 with ⟨lo0, hi0, hc0, hp0⟩
  rcases h1 with ⟨lo1, hi1, hc1, hp1⟩
  rcases h2 with ⟨lo2, hi2, hc2, hp2⟩
  rcases h3 with ⟨lo3, hi3, hc3, hp3⟩
  rcases h4 with ⟨lo4, hi4, hc4, hp4⟩
  rcases h5 with ⟨lo5, hi5, hc5, hp5⟩
  refine ⟨
    ⟨![lo0, lo1, lo2, lo3, lo4, lo5],
      ![hi0, hi1, hi2, hi3, hi4, hi5]⟩, ?_, ?_⟩
  · simp [roots, hc0, hc1, hc2, hc3, hc4, hc5]
  · intro i
    fin_cases i <;> simp at hp0 hp1 hp2 hp3 hp4 hp5 ⊢ <;> assumption

/-- Executable extensional equality for six-dimensional boxes. -/
def boxMatch (left right : Box 6) : Bool :=
  decide (∀ i, left.lo i = right.lo i ∧ left.hi i = right.hi i)

theorem boxMatch_sound {left right : Box 6} (hmatch : boxMatch left right = true) :
    left = right := by
  rw [boxMatch, decide_eq_true_eq] at hmatch
  cases left with
  | mk leftLo leftHi =>
      cases right with
      | mk rightLo rightHi =>
          change ∀ i, leftLo i = rightLo i ∧ leftHi i = rightHi i at hmatch
          congr
          · funext i
            exact (hmatch i).1
          · funext i
            exact (hmatch i).2

/-- Executable, order-sensitive comparison of two root lists. -/
def rootListsMatch : List (Box 6) → List (Box 6) → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      boxMatch left right && rootListsMatch lefts rights
  | _, _ => false

theorem rootListsMatch_sound : ∀ {left right : List (Box 6)},
    rootListsMatch left right = true → left = right := by
  intro left
  induction left with
  | nil =>
      intro right hmatch
      cases right <;> simp [rootListsMatch] at hmatch ⊢
  | cons head tail ih =>
      intro right hmatch
      cases right with
      | nil => simp [rootListsMatch] at hmatch
      | cons other others =>
          rw [rootListsMatch, Bool.and_eq_true] at hmatch
          rw [boxMatch_sound hmatch.1, ih hmatch.2]

/-- Executable comparison between a decoded root artifact and the exact
production Cartesian product. -/
def rootsMatch (decoded : List (Box 6)) : Bool :=
  rootListsMatch decoded roots

theorem rootsMatch_sound {decoded : List (Box 6)}
    (hmatch : rootsMatch decoded = true) : decoded = roots := by
  exact rootListsMatch_sound (by simpa [rootsMatch] using hmatch)

/-- A successfully decoded and matched root blob covers every vector whose
six coordinates lie in the recorded one-body survivor components. -/
theorem decoded_roots_cover
    (blob : ByteArray) (decoded : ProductionRoots)
    (_hdecode : decodeProductionRoots blob = some decoded)
    (hmatch : rootsMatch decoded.1 = true)
    {point : Fin 6 → ℕ}
    (hcovered : ∀ i, coordinateCovered i (point i)) :
    Forest.Covers decoded.1 point := by
  rw [rootsMatch_sound hmatch]
  exact covers_roots hcovered

/-! ## Exact replay of initialization's one-body pruning -/

/-- Scaled one-body score used to decide whether a single grid cell survives
initialization.  Its two summands are exactly pressure and the adjacent-pair
term for the selected coordinate. -/
def oneBodyScore (data : RangeKernelTable) (coordinate : Fin 6)
    (cell : Fin data.table.cellCount) : ℤ :=
  pressureCoefficient data.table.scaleBits * (cell.1 : ℤ) +
    pairCoefficient data.table.grid coordinate.1 (coordinate.1 + 1) *
      data.table.value cell

/-- Exact normalization of the integer one-body score. -/
theorem oneBodyScore_div_scale (data : RangeKernelTable) (coordinate : Fin 6)
    (cell : Fin data.table.cellCount) (hgrid : 0 < data.table.grid) :
    (oneBodyScore data coordinate cell : ℝ) /
        scale data.table.grid data.table.scaleBits =
      Zeta23Ext.Weighted.pressure * ((cell.1 : ℝ) / data.table.grid) +
        Zeta23Ext.Weighted.pairWeight coordinate.1 (coordinate.1 + 1) *
          ((data.table.value cell : ℝ) / (2 : ℝ) ^ data.table.scaleBits) := by
  unfold oneBodyScore
  rw [Int.cast_add, add_div, pressureTerm_div_scale hgrid,
    pairTerm_div_scale hgrid]

/-- One coordinate's pressure and adjacent-pair terms occur in the full
six-gap objective. -/
theorem oneBody_le_F6 (gaps : CurrentGapVector) (coordinate : Fin 6) :
    Zeta23Ext.Weighted.pressure * gaps.1 coordinate +
        Zeta23Ext.Weighted.pairWeight coordinate.1 (coordinate.1 + 1) *
          CurrentWindow.weight (gaps.1 coordinate) ≤
      Zeta23Ext.Weighted.F6 CurrentWindow.weight gaps.1 := by
  unfold Zeta23Ext.Weighted.F6 Zeta23Ext.Weighted.F6With
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ Zeta23Ext.Weighted.pressure_nonneg
    exact Finset.single_le_sum (fun i _ => gaps.2 i) (Finset.mem_univ coordinate)
  · calc
      Zeta23Ext.Weighted.pairWeight coordinate.1 (coordinate.1 + 1) *
            CurrentWindow.weight (gaps.1 coordinate)
          = Zeta23Ext.Weighted.pairWeight coordinate.1 (coordinate.1 + 1) *
              CurrentWindow.weight
                (∑ t ∈ Finset.Ico coordinate.1 (coordinate.1 + 1),
                  Aggregation.gext gaps.1 t) := by
              congr 2
              simp [Aggregation.gext, coordinate.2]
      _ ≤ ∑ i ∈ Finset.range (7 - 1),
            Zeta23Ext.Weighted.pairWeight i (i + 1) *
              CurrentWindow.weight
                (∑ t ∈ Finset.Ico i (i + 1), Aggregation.gext gaps.1 t) := by
          apply Finset.single_le_sum
            (s := Finset.range (7 - 1))
            (f := fun i =>
              Zeta23Ext.Weighted.pairWeight i (i + 1) *
                CurrentWindow.weight
                  (∑ t ∈ Finset.Ico i (i + 1), Aggregation.gext gaps.1 t))
          · intro i hi
            exact mul_nonneg (Zeta23Ext.Weighted.pairWeight_nonneg _ _)
              (CurrentWindow.weight_nonneg _)
          · simp
      _ ≤ ∑ r ∈ Finset.Icc (1 : ℕ) 6,
            ∑ i ∈ Finset.range (7 - r),
              Zeta23Ext.Weighted.pairWeight i (i + r) *
                CurrentWindow.weight
                  (∑ t ∈ Finset.Ico i (i + r), Aggregation.gext gaps.1 t) := by
          apply Finset.single_le_sum
            (s := Finset.Icc (1 : ℕ) 6)
            (f := fun r =>
              ∑ i ∈ Finset.range (7 - r),
                Zeta23Ext.Weighted.pairWeight i (i + r) *
                  CurrentWindow.weight
                    (∑ t ∈ Finset.Ico i (i + r), Aggregation.gext gaps.1 t))
          · intro r hr
            exact Finset.sum_nonneg fun i _ =>
              mul_nonneg (Zeta23Ext.Weighted.pairWeight_nonneg _ _)
                (CurrentWindow.weight_nonneg _)
          · simp

/-- Soundness of a successful integer one-body comparison for the real gap
located in that cell. -/
theorem oneBodyScore_implies_local (data : RangeKernelTable)
    (hsound : data.table.Sound CurrentWindow.weight)
    (gaps : CurrentGapVector) (coordinate : Fin 6)
    (hcell : gridCell data.table.grid (gaps.1 coordinate) < data.table.cellCount)
    (hscore : target data.table.grid data.table.scaleBits ≤
      oneBodyScore data coordinate
        ⟨gridCell data.table.grid (gaps.1 coordinate), hcell⟩) :
    Zeta23Ext.Weighted.beta ≤
      Zeta23Ext.Weighted.F6 CurrentWindow.weight gaps.1 := by
  let cell : Fin data.table.cellCount :=
    ⟨gridCell data.table.grid (gaps.1 coordinate), hcell⟩
  have htable := hsound.2 cell (gaps.1 coordinate)
    (gridCell_lower hsound.1 (gaps.2 coordinate))
    (gridCell_upper hsound.1 _).le
  rw [show Zeta23Ext.Weighted.beta =
      (target data.table.grid data.table.scaleBits : ℝ) /
        scale data.table.grid data.table.scaleBits by
      symm
      exact target_div_scale hsound.1]
  calc
    (target data.table.grid data.table.scaleBits : ℝ) /
          scale data.table.grid data.table.scaleBits
        ≤ (oneBodyScore data coordinate cell : ℝ) /
            scale data.table.grid data.table.scaleBits :=
      div_le_div_of_nonneg_right (by exact_mod_cast hscore)
        (le_of_lt (scale_pos hsound.1))
    _ = Zeta23Ext.Weighted.pressure * ((cell.1 : ℝ) / data.table.grid) +
          Zeta23Ext.Weighted.pairWeight coordinate.1 (coordinate.1 + 1) *
            ((data.table.value cell : ℝ) / (2 : ℝ) ^ data.table.scaleBits) :=
      oneBodyScore_div_scale data coordinate cell hsound.1
    _ ≤ Zeta23Ext.Weighted.pressure * gaps.1 coordinate +
          Zeta23Ext.Weighted.pairWeight coordinate.1 (coordinate.1 + 1) *
            CurrentWindow.weight (gaps.1 coordinate) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (gridCell_lower hsound.1 (gaps.2 coordinate))
          Zeta23Ext.Weighted.pressure_nonneg
      · exact mul_le_mul_of_nonneg_left htable
          (Zeta23Ext.Weighted.pairWeight_nonneg _ _)
    _ ≤ Zeta23Ext.Weighted.F6 CurrentWindow.weight gaps.1 :=
      oneBody_le_F6 gaps coordinate

/-- One finite initialization cell passes if it is retained in a recorded
component or its exact integer one-body score reaches the target. -/
def initialCellOK (data : RangeKernelTable)
    (hcutoff : pressureCutoff ≤ data.table.cellCount)
    (coordinate : Fin 6) (cell : Fin pressureCutoff) : Bool :=
  if coordinateCoveredBool coordinate cell.1 then true
  else
    decide (target data.table.grid data.table.scaleBits ≤
      oneBodyScore data coordinate
        ⟨cell.1, lt_of_lt_of_le cell.2 hcutoff⟩)

/-- Executable replay of all `6 * 46830` one-body initialization decisions. -/
def initialCheck (data : RangeKernelTable)
    (hcutoff : pressureCutoff ≤ data.table.cellCount) : Bool :=
  (List.ofFn fun coordinate : Fin 6 => coordinate).all fun coordinate =>
    (List.ofFn fun cell : Fin pressureCutoff => cell).all fun cell =>
      initialCellOK data hcutoff coordinate cell

theorem initialCheck_cell (data : RangeKernelTable)
    (hcutoff : pressureCutoff ≤ data.table.cellCount)
    (hcheck : initialCheck data hcutoff = true)
    (coordinate : Fin 6) (cell : Fin pressureCutoff)
    (hexcluded : ¬ coordinateCovered coordinate cell.1) :
    target data.table.grid data.table.scaleBits ≤
      oneBodyScore data coordinate
        ⟨cell.1, lt_of_lt_of_le cell.2 hcutoff⟩ := by
  rw [initialCheck, List.all_eq_true] at hcheck
  have hcoordinate := hcheck coordinate (List.mem_ofFn.mpr ⟨coordinate, rfl⟩)
  rw [List.all_eq_true] at hcoordinate
  have hcell := hcoordinate cell (List.mem_ofFn.mpr ⟨cell, rfl⟩)
  have hfalse : coordinateCoveredBool coordinate cell.1 = false := by
    apply Bool.eq_false_iff.mpr
    simpa [coordinateCovered] using hexcluded
  simp [initialCellOK, hfalse] at hcell
  exact hcell

/-- Kernel-checked finite evidence for production one-body initialization. -/
structure InitialOneBodyCertificate (data : RangeKernelTable) where
  cutoff_le_cellCount : pressureCutoff ≤ data.table.cellCount
  checked : initialCheck data cutoff_le_cellCount = true

/-- Pressure pruning, exact one-body pruning, and explicit root coverage give
the complete initialization case split used before forest subdivision. -/
theorem initial_classify (data : RangeKernelTable)
    (hgrid : data.table.grid = 4000)
    (hsound : data.table.Sound CurrentWindow.weight)
    (certificate : InitialOneBodyCertificate data)
    (gaps : CurrentGapVector) :
    Zeta23Ext.Weighted.beta ≤
        Zeta23Ext.Weighted.F6 CurrentWindow.weight gaps.1 ∨
      Forest.Covers roots (locateGaps data.table.grid gaps) := by
  by_cases hpressure : pressureCutoff ≤
      pointSum (locateGaps data.table.grid gaps)
  · left
    have hpressure' : pressureCutoff ≤ pointSum (locateGaps 4000 gaps) := by
      simpa [hgrid] using hpressure
    exact pressure_cutoff_local data.table.scaleBits gaps hpressure'
  · have hbelow : ∀ i, locateGaps data.table.grid gaps i < pressureCutoff := by
      intro i
      have hsingle : locateGaps data.table.grid gaps i ≤
          pointSum (locateGaps data.table.grid gaps) := by
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      omega
    by_cases hall : ∀ i, coordinateCovered i (locateGaps data.table.grid gaps i)
    · right
      exact covers_roots hall
    · left
      push Not at hall
      obtain ⟨coordinate, hexcluded⟩ := hall
      let cell : Fin pressureCutoff :=
        ⟨locateGaps data.table.grid gaps coordinate, hbelow coordinate⟩
      apply oneBodyScore_implies_local data hsound gaps coordinate
        (lt_of_lt_of_le cell.2 certificate.cutoff_le_cellCount)
      exact initialCheck_cell data certificate.cutoff_le_cellCount
        certificate.checked coordinate cell hexcluded

/-- The finite initialization checker supplies the previously abstract
outside-root branch of the real forest bridge. -/
noncomputable def forestBridge (data : RangeKernelTable) (decoded : ProductionRoots)
    (hmatch : rootsMatch decoded.1 = true)
    (hgrid : data.table.grid = 4000)
    (hsound : data.table.Sound CurrentWindow.weight)
    (certificate : InitialOneBodyCertificate data) :
    ForestRealBridge (CurrentReplay.problem data) decoded.1 CurrentGapVector
      fun gaps => Zeta23Ext.Weighted.beta ≤
        Zeta23Ext.Weighted.F6 CurrentWindow.weight gaps.1 where
  locate := locateGaps data.table.grid
  classify := fun gaps => by
    rcases initial_classify data hgrid hsound certificate gaps with hlocal | hcover
    · exact Or.inl hlocal
    · exact Or.inr (by simpa [rootsMatch_sound hmatch] using hcover)
  transfer := fun gaps hscore =>
    target_le_exactScore_implies_local data hsound gaps hscore

/-- End-to-end theorem interface for the two decoded production artifacts.
Every initialization decision is replayed by `initialCheck`; the remaining
forest premise is precisely leaf arithmetic (including tangent leaves). -/
theorem currentLocalCertificate_of_decoded_replay
    (treeBlob rootBlob : ByteArray)
    (trees : ProductionForest) (decoded : ProductionRoots)
    (data : RangeKernelTable)
    (_htrees : decodeProductionForest treeBlob = some trees)
    (_hroots : decodeProductionRoots rootBlob = some decoded)
    (hmatch : rootsMatch decoded.1 = true)
    (hgrid : data.table.grid = 4000)
    (hsound : data.table.Sound CurrentWindow.weight)
    (initial : InitialOneBodyCertificate data)
    (hcheck : Forest.check (CurrentReplay.problem data).leafOK trees.1 decoded.1 = true) :
    CurrentWindow.LocalCertificate :=
  currentLocalCertificate_of_checked_forest (CurrentReplay.problem data)
    decoded.1 trees.1 (forestBridge data decoded hmatch hgrid hsound initial) hcheck

end Zeta23Ext.VerifiedCertificate.CurrentInitialRoots
