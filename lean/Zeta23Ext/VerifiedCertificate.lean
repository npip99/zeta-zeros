/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindow

/-!
# Kernel-checked core for exported interval-tree certificates

The production Python search previously left only a summary.  This module
defines the small proof-producing format needed to replay its subdivision in
Lean.  The tree checker verifies every split and every integer lower-bound
comparison.  Its soundness theorem proves coverage of every lattice point in
the root box.

For the current cosine window, the remaining non-rational obligation is
isolated as `DyadicKernelTable.Sound`: each exported dyadic table entry must be
a lower bound for the true transcendental kernel square on its grid cell.
Once a concrete `lowerScore_sound` theorem is built from that table, no trust
in Python's branch traversal or floating-point additions is needed.
-/

namespace Zeta23Ext.VerifiedCertificate

/-! ## Boxes and a proof-producing subdivision tree -/

/-- An inclusive integer box in `q` coordinates. -/
structure Box (q : ℕ) where
  lo : Fin q → ℕ
  hi : Fin q → ℕ

/-- Membership in an inclusive integer box. -/
def Box.Contains {q : ℕ} (b : Box q) (x : Fin q → ℕ) : Prop :=
  ∀ i, b.lo i ≤ x i ∧ x i ≤ b.hi i

/-- Midpoint used by the Python verifier. -/
def Box.mid {q : ℕ} (b : Box q) (i : Fin q) : ℕ :=
  (b.lo i + b.hi i) / 2

/-- Inclusive lower half of a box. -/
def Box.left {q : ℕ} (b : Box q) (i : Fin q) : Box q :=
  ⟨b.lo, Function.update b.hi i (b.mid i)⟩

/-- Inclusive upper half of a box. -/
def Box.right {q : ℕ} (b : Box q) (i : Fin q) : Box q :=
  ⟨Function.update b.lo i (b.mid i + 1), b.hi⟩

/-- Every lattice point in a parent box belongs to one of its two midpoint
children.  This is the coverage fact that a summary-only certificate lacked. -/
lemma Box.contains_left_or_right {q : ℕ} {b : Box q} {x : Fin q → ℕ}
    (hx : b.Contains x) (i : Fin q) :
    (b.left i).Contains x ∨ (b.right i).Contains x := by
  by_cases hxi : x i ≤ b.mid i
  · left
    intro j
    constructor
    · exact (hx j).1
    · by_cases hji : j = i
      · subst j
        simpa [Box.left] using hxi
      · simpa [Box.left, hji] using (hx j).2
  · right
    intro j
    constructor
    · by_cases hji : j = i
      · subst j
        simp only [Box.right, Function.update_self]
        omega
      · simpa [Box.right, hji] using (hx j).1
    · exact (hx j).2

/-- Preorder proof tree.  A split coordinate is part of the certificate;
children are always reconstructed by the checker, so malformed child boxes
cannot be smuggled into an exported artifact. -/
inductive Tree (q : ℕ) where
  | leaf
  | split (coordinate : Fin q) (lower upper : Tree q)

/-- Replay a certificate against an executable leaf predicate. -/
def Tree.check {q : ℕ} (leafOK : Box q → Bool) : Tree q → Box q → Bool
  | .leaf, b => leafOK b
  | .split i lower upper, b =>
      lower.check leafOK (b.left i) && upper.check leafOK (b.right i)

/-- Soundness of the structural checker: if accepted leaves establish `P`
for all lattice points in their boxes, an accepted tree establishes `P` on
its entire root box. -/
theorem Tree.check_sound {q : ℕ} {leafOK : Box q → Bool}
    {P : (Fin q → ℕ) → Prop}
    (hleaf : ∀ b, leafOK b = true → ∀ x, b.Contains x → P x) :
    ∀ (tree : Tree q) (root : Box q), tree.check leafOK root = true →
      ∀ x, root.Contains x → P x := by
  intro tree
  induction tree with
  | leaf =>
      intro root hcheck x hx
      exact hleaf root hcheck x hx
  | split i lower upper ihLower ihUpper =>
      intro root hcheck x hx
      rw [Tree.check, Bool.and_eq_true] at hcheck
      rcases root.contains_left_or_right hx i with hleft | hright
      · exact ihLower (root.left i) hcheck.1 x hleft
      · exact ihUpper (root.right i) hcheck.2 x hright

/-! ## Exact scaled-integer leaf arithmetic -/

/-- Data needed to validate the rational part of a branch-and-bound proof.

`exactScore` is the scaled objective at lattice cells; `lowerScore` is the
box lower bound computed from dyadic kernel-table minima and exact rational
weights.  The sole mathematical input to this layer is `lowerScore_sound`.
-/
structure IntegerLowerBoundProblem (q : ℕ) where
  target : ℤ
  exactScore : (Fin q → ℕ) → ℤ
  lowerScore : Box q → ℤ
  lowerScore_sound :
    ∀ b x, b.Contains x → lowerScore b ≤ exactScore x

/-- A leaf is accepted precisely when exact integer arithmetic proves its
box lower bound reaches the target. -/
def IntegerLowerBoundProblem.leafOK {q : ℕ}
    (problem : IntegerLowerBoundProblem q) (b : Box q) : Bool :=
  decide (problem.target ≤ problem.lowerScore b)

/-- Kernel-checked arithmetic and coverage theorem for an exported tree. -/
theorem IntegerLowerBoundProblem.checked_tree_sound {q : ℕ}
    (problem : IntegerLowerBoundProblem q) (tree : Tree q) (root : Box q)
    (hcheck : tree.check problem.leafOK root = true) :
    ∀ x, root.Contains x → problem.target ≤ problem.exactScore x := by
  refine Tree.check_sound (P := fun x => problem.target ≤ problem.exactScore x)
    ?_ tree root hcheck
  intro b hleaf x hx
  rw [IntegerLowerBoundProblem.leafOK, decide_eq_true_eq] at hleaf
  exact hleaf.trans (problem.lowerScore_sound b x hx)

/-- Bridge from a checked integer certificate to an arbitrary real-domain
conclusion.  For the current application, `locate_mem` is ordinary grid-cell
location and `transfer` follows from exact rational weights plus the sound
dyadic kernel table.  Neither tree coverage nor branch arithmetic appears in
these remaining obligations. -/
structure RealBridge {q : ℕ} (problem : IntegerLowerBoundProblem q)
    (root : Box q) (X : Type*) (Conclusion : X → Prop) where
  locate : X → Fin q → ℕ
  locate_mem : ∀ x, root.Contains (locate x)
  transfer : ∀ x, problem.target ≤ problem.exactScore (locate x) → Conclusion x

/-- A checked tree and a real-domain bridge prove the real conclusion. -/
theorem RealBridge.checked_sound {q : ℕ} {problem : IntegerLowerBoundProblem q}
    {root : Box q} {X : Type*} {Conclusion : X → Prop}
    (bridge : RealBridge problem root X Conclusion) (tree : Tree q)
    (hcheck : tree.check problem.leafOK root = true) : ∀ x, Conclusion x := by
  intro x
  exact bridge.transfer x
    (problem.checked_tree_sound tree root hcheck (bridge.locate x) (bridge.locate_mem x))

/-- Nonnegative six-gap vectors, the domain of the current local inequality. -/
def CurrentGapVector := {g : Fin 6 → ℝ // ∀ i, 0 ≤ g i}

/-- Exact final connection to `CurrentWindow.LocalCertificate`.  A concrete
export now needs only an accepted tree and a `RealBridge`; the latter is where
the formal dyadic-table bounds are consumed. -/
theorem currentLocalCertificate_of_checked_tree
    (problem : IntegerLowerBoundProblem 6) (root : Box 6) (tree : Tree 6)
    (bridge : RealBridge problem root CurrentGapVector fun g =>
      Weighted.beta ≤ Weighted.F6 CurrentWindow.weight g.1)
    (hcheck : tree.check problem.leafOK root = true) :
    CurrentWindow.LocalCertificate := by
  intro g hg
  exact bridge.checked_sound tree hcheck ⟨g, hg⟩

/-! ## The deliberately narrow transcendental obligation -/

/-- Dyadic lower-bound table for a real kernel weight.  Values are interpreted
as `value / 2^scaleBits` on cells `[i/grid,(i+1)/grid]`. -/
structure DyadicKernelTable where
  grid : ℕ
  scaleBits : ℕ
  cellCount : ℕ
  value : Fin cellCount → ℤ

/-- Exact proposition a future formal sinc/cosine interval evaluator must
discharge.  It contains no branch-tree or objective-arithmetic assertion. -/
def DyadicKernelTable.Sound (table : DyadicKernelTable) (weight : ℝ → ℝ) : Prop :=
  0 < table.grid ∧ ∀ i : Fin table.cellCount, ∀ x : ℝ,
    (i : ℝ) / table.grid ≤ x →
    x ≤ ((i : ℕ) + 1 : ℝ) / table.grid →
    (table.value i : ℝ) / (2 : ℝ) ^ table.scaleBits ≤ weight x

/-! ## Small executable regression certificate -/

namespace Demo

/-- Singleton-sensitive lower bound: subdivision is genuinely required. -/
def exactScore (x : Fin 1 → ℕ) : ℤ := if x 0 < 4 then 1 else 0

def lowerScore (b : Box 1) : ℤ :=
  if b.lo 0 = b.hi 0 ∧ b.hi 0 < 4 then 1 else 0

lemma lowerScore_sound : ∀ b x, b.Contains x → lowerScore b ≤ exactScore x := by
  intro b x hx
  unfold lowerScore exactScore
  split_ifs with hbox hx4
  · norm_num
  · simp only [not_lt] at hx4
    have := (hx 0).2
    omega
  · omega
  · norm_num

def problem : IntegerLowerBoundProblem 1 :=
  ⟨1, exactScore, lowerScore, lowerScore_sound⟩

def root : Box 1 := ⟨fun _ => 0, fun _ => 3⟩

/-- Four singleton leaves covering `[0,3]`. -/
def tree : Tree 1 :=
  .split 0 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)

theorem tree_checked : tree.check problem.leafOK root = true := by
  decide

theorem all_root_cells_verified (x : Fin 1 → ℕ) (hx : root.Contains x) :
    problem.target ≤ problem.exactScore x :=
  problem.checked_tree_sound tree root tree_checked x hx

end Demo

end Zeta23Ext.VerifiedCertificate
