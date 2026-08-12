/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.VerifiedCertificateForest

/-!
# Reusable arithmetic components for finite interval certificates

This module discharges two purely structural obligations left abstract by
`IntegerLowerBoundProblem` and `RealBridge`:

* a box lower score assembled from finitely many independently sound integer
  term bounds is sound for the summed point score; and
* flooring a nonnegative real gap after multiplication by a positive grid
  locates it in the corresponding half-open grid cell.

These results do not provide the missing transcendental kernel-table bounds,
the production root boxes, or the production tree artifact.
-/

namespace Zeta23Ext.VerifiedCertificate

noncomputable section

/-! ## Termwise construction of `lowerScore_sound` -/

/-- A finite collection of exact integer score terms and boxwise lower terms. -/
structure TermwiseIntegerBounds (q termCount : ℕ) where
  exactTerm : Fin termCount → (Fin q → ℕ) → ℤ
  lowerTerm : Fin termCount → Box q → ℤ
  lowerTerm_sound :
    ∀ term box point, box.Contains point →
      lowerTerm term box ≤ exactTerm term point

/-- Exact point score obtained by summing all terms. -/
def TermwiseIntegerBounds.exactScore {q termCount : ℕ}
    (data : TermwiseIntegerBounds q termCount) (point : Fin q → ℕ) : ℤ :=
  ∑ term, data.exactTerm term point

/-- Box score obtained by summing all termwise lower bounds. -/
def TermwiseIntegerBounds.lowerScore {q termCount : ℕ}
    (data : TermwiseIntegerBounds q termCount) (box : Box q) : ℤ :=
  ∑ term, data.lowerTerm term box

/-- Termwise lower-bound soundness is preserved by the exact finite sum. -/
theorem TermwiseIntegerBounds.lowerScore_sound {q termCount : ℕ}
    (data : TermwiseIntegerBounds q termCount) (box : Box q)
    (point : Fin q → ℕ) (hpoint : box.Contains point) :
    data.lowerScore box ≤ data.exactScore point := by
  unfold TermwiseIntegerBounds.lowerScore TermwiseIntegerBounds.exactScore
  exact Finset.sum_le_sum fun term _ => data.lowerTerm_sound term box point hpoint

/-- Package termwise sound bounds as the integer problem consumed by the tree
checker.  The target remains independent exact certificate data. -/
def TermwiseIntegerBounds.toProblem {q termCount : ℕ}
    (data : TermwiseIntegerBounds q termCount) (target : ℤ) :
    IntegerLowerBoundProblem q where
  target := target
  exactScore := data.exactScore
  lowerScore := data.lowerScore
  lowerScore_sound := data.lowerScore_sound

/-! ## Exact pressure lower term -/

/-- The sum of lower endpoints of an integer box. -/
def Box.sumLo {q : ℕ} (box : Box q) : ℕ :=
  ∑ i, box.lo i

/-- The coordinate sum of a lattice point. -/
def pointSum {q : ℕ} (point : Fin q → ℕ) : ℕ :=
  ∑ i, point i

/-- Coordinatewise box membership bounds the sum by the lower endpoints. -/
theorem Box.sumLo_le_pointSum {q : ℕ} {box : Box q}
    {point : Fin q → ℕ} (hpoint : box.Contains point) :
    box.sumLo ≤ pointSum point := by
  unfold Box.sumLo pointSum
  exact Finset.sum_le_sum fun i _ => (hpoint i).1

/-- Multiplying the pressure term by a nonnegative exact integer coefficient
preserves the box lower bound. -/
theorem Box.pressure_lower_sound {q coefficient : ℕ} {box : Box q}
    {point : Fin q → ℕ} (hpoint : box.Contains point) :
    (coefficient * box.sumLo : ℤ) ≤ (coefficient * pointSum point : ℕ) := by
  exact_mod_cast Nat.mul_le_mul_left coefficient (Box.sumLo_le_pointSum hpoint)

/-! ## Kernel-checked grid location -/

/-- Cell index used by the verifier for a nonnegative real coordinate. -/
def gridCell (grid : ℕ) (x : ℝ) : ℕ :=
  ⌊(grid : ℝ) * x⌋₊

/-- A nonnegative coordinate lies weakly above its grid-cell lower endpoint. -/
theorem gridCell_lower {grid : ℕ} (hgrid : 0 < grid) {x : ℝ} (hx : 0 ≤ x) :
    (gridCell grid x : ℝ) / grid ≤ x := by
  have hfloor : (gridCell grid x : ℝ) ≤ (grid : ℝ) * x := by
    exact Nat.floor_le (mul_nonneg (by positivity) hx)
  exact (div_le_iff₀ (by exact_mod_cast hgrid)).2 (by simpa [mul_comm] using hfloor)

/-- A nonnegative coordinate lies strictly below its grid-cell upper endpoint. -/
theorem gridCell_upper {grid : ℕ} (hgrid : 0 < grid) (x : ℝ) :
    x < ((gridCell grid x : ℕ) + 1 : ℝ) / grid := by
  have hfloor : (grid : ℝ) * x < (gridCell grid x : ℝ) + 1 := by
    simpa [gridCell] using (Nat.lt_floor_add_one ((grid : ℝ) * x))
  exact (lt_div_iff₀ (by exact_mod_cast hgrid)).2 (by simpa [mul_comm] using hfloor)

/-- Coordinatewise grid location for a nonnegative real vector. -/
def locateOnGrid {q : ℕ} (grid : ℕ)
    (point : {x : Fin q → ℝ // ∀ i, 0 ≤ x i}) : Fin q → ℕ :=
  fun i => gridCell grid (point.1 i)

/-- Every coordinate lies in the half-open cell selected by `locateOnGrid`. -/
theorem locateOnGrid_cell {q grid : ℕ} (hgrid : 0 < grid)
    (point : {x : Fin q → ℝ // ∀ i, 0 ≤ x i}) (i : Fin q) :
    ((locateOnGrid grid point i : ℕ) : ℝ) / grid ≤ point.1 i ∧
      point.1 i < ((locateOnGrid grid point i : ℕ) + 1 : ℝ) / grid := by
  exact ⟨gridCell_lower hgrid (point.2 i), gridCell_upper hgrid _⟩

/-! ## Composing a forest bridge from explicit classification and transfer -/

/-- Construct the real bridge used by forest replay from the canonical grid
locator.  The two remaining arguments are precisely the application-specific
initial-pruning classification and score-to-real transfer proofs. -/
def ForestRealBridge.onGrid {q grid : ℕ} (_hgrid : 0 < grid)
    {problem : IntegerLowerBoundProblem q} {roots : List (Box q)}
    {Conclusion : {x : Fin q → ℝ // ∀ i, 0 ≤ x i} → Prop}
    (classify : ∀ x, Conclusion x ∨ Forest.Covers roots (locateOnGrid grid x))
    (transfer : ∀ x,
      problem.target ≤ problem.exactScore (locateOnGrid grid x) → Conclusion x) :
    ForestRealBridge problem roots
      {x : Fin q → ℝ // ∀ i, 0 ≤ x i} Conclusion where
  locate := locateOnGrid grid
  classify := classify
  transfer := transfer

end

end Zeta23Ext.VerifiedCertificate
