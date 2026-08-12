/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.VerifiedCertificate

/-!
# Forest replay and the `Z23TREE1` topology decoder

The production interval search starts from 324 boxes, so its subdivision
artifact is a forest rather than a single tree.  This module extends the
kernel-checked replay layer accordingly and gives an executable decoder for
the exact byte layout emitted by `proof_certificate/export_interval_tree.py`.

The decoder accepts only the current six-gap production metadata: dimension
6, 324 roots, and 1,739,356 nodes.  It reconstructs every split coordinate
from the preorder token stream, rejects malformed arities and trailing bytes,
and returns actual `Tree 6` values that can be fed directly to `Forest.check`.

The production `.tree` and root-box files are external certificate artifacts,
not definitions embedded into this module.  Thus this module proves what
acceptance of those bytes means; it does not turn their presence into a
theorem or bypass leaf arithmetic.
-/

namespace Zeta23Ext.VerifiedCertificate

/-! ## Forest coverage and replay -/

/-- Number of nodes in a proof tree. -/
def Tree.nodeCount {q : ℕ} : Tree q → ℕ
  | .leaf => 1
  | .split _ lower upper => 1 + lower.nodeCount + upper.nodeCount

/-- Number of split nodes in a proof tree. -/
def Tree.splitCount {q : ℕ} : Tree q → ℕ
  | .leaf => 0
  | .split _ lower upper => 1 + lower.splitCount + upper.splitCount

/-- Number of leaves in a proof tree. -/
def Tree.leafCount {q : ℕ} : Tree q → ℕ
  | .leaf => 1
  | .split _ lower upper => lower.leafCount + upper.leafCount

/-- Every tree is full binary: leaves are splits plus one. -/
theorem Tree.leafCount_eq_splitCount_add_one {q : ℕ} (tree : Tree q) :
    tree.leafCount = tree.splitCount + 1 := by
  induction tree with
  | leaf => rfl
  | split coordinate lower upper ihLower ihUpper =>
      simp only [Tree.leafCount, Tree.splitCount, ihLower, ihUpper]
      omega

/-- Node count is the sum of split and leaf counts. -/
theorem Tree.nodeCount_eq_splitCount_add_leafCount {q : ℕ} (tree : Tree q) :
    tree.nodeCount = tree.splitCount + tree.leafCount := by
  induction tree with
  | leaf => rfl
  | split coordinate lower upper ihLower ihUpper =>
      simp only [Tree.nodeCount, Tree.splitCount, Tree.leafCount, ihLower, ihUpper]
      omega

/-- Full-binary invariant for an arbitrary forest. -/
theorem Forest.sum_leafCount_eq_sum_splitCount_add_length {q : ℕ}
    (trees : List (Tree q)) :
    (trees.map Tree.leafCount).sum =
      (trees.map Tree.splitCount).sum + trees.length := by
  induction trees with
  | nil => rfl
  | cons tree trees ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Tree.leafCount_eq_splitCount_add_one, ih]
      omega

/-- The committed report's aggregate counts satisfy the necessary 324-root
full-binary-forest identity.  This checks only summary consistency, not the
missing subdivision topology. -/
theorem production_report_count_identity : 869840 = 869516 + 324 := by
  norm_num

/-- Replay corresponding trees and roots.  Unequal list lengths are rejected. -/
def Forest.check {q : ℕ} (leafOK : Box q → Bool) :
    List (Tree q) → List (Box q) → Bool
  | [], [] => true
  | tree :: trees, root :: roots =>
      tree.check leafOK root && Forest.check leafOK trees roots
  | _, _ => false

/-- A point belongs to at least one root of a forest. -/
def Forest.Covers {q : ℕ} (roots : List (Box q)) (x : Fin q → ℕ) : Prop :=
  ∃ root ∈ roots, root.Contains x

/-- Checked forest replay proves the leaf conclusion on every covered point. -/
theorem Forest.check_sound {q : ℕ} {leafOK : Box q → Bool}
    {P : (Fin q → ℕ) → Prop}
    (hleaf : ∀ b, leafOK b = true → ∀ x, b.Contains x → P x) :
    ∀ trees roots, Forest.check leafOK trees roots = true →
      ∀ x, Forest.Covers roots x → P x := by
  intro trees
  induction trees with
  | nil =>
      intro roots hcheck x hcover
      cases roots with
      | nil => simp [Forest.Covers] at hcover
      | cons root roots => simp [Forest.check] at hcheck
  | cons tree trees ih =>
      intro roots hcheck x hcover
      cases roots with
      | nil => simp [Forest.check] at hcheck
      | cons root roots =>
          rw [Forest.check, Bool.and_eq_true] at hcheck
          rcases hcover with ⟨covered, hmem, hx⟩
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | htail
          · rw [heq] at hx
            exact Tree.check_sound hleaf tree root hcheck.1 x hx
          · exact ih roots hcheck.2 x ⟨covered, htail, hx⟩

/-- Integer soundness specialized to a checked forest. -/
theorem IntegerLowerBoundProblem.checked_forest_sound {q : ℕ}
    (problem : IntegerLowerBoundProblem q) (trees : List (Tree q))
    (roots : List (Box q))
    (hcheck : Forest.check problem.leafOK trees roots = true) :
    ∀ x, Forest.Covers roots x → problem.target ≤ problem.exactScore x := by
  refine Forest.check_sound (P := fun x => problem.target ≤ problem.exactScore x)
    ?_ trees roots hcheck
  intro b hleaf x hx
  rw [IntegerLowerBoundProblem.leafOK, decide_eq_true_eq] at hleaf
  exact hleaf.trans (problem.lowerScore_sound b x hx)

/-! ## A bridge honest about initialization pruning -/

/-- Real-domain bridge for a forest.

The initial 324 production boxes cover only the coordinate components that
survive the verifier's one-body pruning.  Consequently `classify` permits a
real input either to be discharged directly (`Conclusion x`) or to be located
inside one of the checked roots.  This prevents the forest interface from
silently assuming that the production roots cover the whole orthant.
-/
structure ForestRealBridge {q : ℕ} (problem : IntegerLowerBoundProblem q)
    (roots : List (Box q)) (X : Type*) (Conclusion : X → Prop) where
  locate : X → Fin q → ℕ
  classify : ∀ x, Conclusion x ∨ Forest.Covers roots (locate x)
  transfer : ∀ x, problem.target ≤ problem.exactScore (locate x) → Conclusion x

/-- Checked forest replay plus the outside-root discharge proves the real conclusion. -/
theorem ForestRealBridge.checked_sound {q : ℕ}
    {problem : IntegerLowerBoundProblem q} {trees : List (Tree q)}
    {roots : List (Box q)} {X : Type*} {Conclusion : X → Prop}
    (bridge : ForestRealBridge problem roots X Conclusion)
    (hcheck : Forest.check problem.leafOK trees roots = true) :
    ∀ x, Conclusion x := by
  intro x
  rcases bridge.classify x with hx | hx
  · exact hx
  · exact bridge.transfer x (problem.checked_forest_sound trees roots hcheck _ hx)

/-- Exact current-window connection for the 324-root forest layout. -/
theorem currentLocalCertificate_of_checked_forest
    (problem : IntegerLowerBoundProblem 6) (roots : List (Box 6))
    (trees : List (Tree 6))
    (bridge : ForestRealBridge problem roots CurrentGapVector fun g =>
      Weighted.beta ≤ Weighted.F6 CurrentWindow.weight g.1)
    (hcheck : Forest.check problem.leafOK trees roots = true) :
    CurrentWindow.LocalCertificate := by
  intro g hg
  exact bridge.checked_sound hcheck ⟨g, hg⟩

/-! ## Executable `Z23TREE1` decoder -/

/-- Production metadata recorded by the current report. -/
def productionRootCount : ℕ := 324

/-- Production node count recorded by the current report. -/
def productionNodeCount : ℕ := 1739356

/-- A decoded topology carries the kernel-checked fact that it has the
production report's 324 roots. -/
def ProductionForest :=
  {trees : List (Tree 6) // trees.length = productionRootCount}

/-- Interpret a fixed-width sequence as an unsigned big-endian integer. -/
def bigEndianNat (bytes : List UInt8) : ℕ :=
  bytes.foldl (fun value byte => 256 * value + byte.toNat) 0

/-- Parse one preorder tree.  `fuel` bounds recursive calls; successful output
always comes solely from consumed tokens, while malformed or truncated input
returns `none`. -/
def decodeTree (q fuel : ℕ) : List UInt8 → Option (Tree q × List UInt8)
  | [] => none
  | token :: rest =>
      if hzero : token.toNat = 0 then
        some (.leaf, rest)
      else if hq : token.toNat ≤ q then
        match fuel with
        | 0 => none
        | fuel + 1 =>
            have hpos : 0 < token.toNat := Nat.pos_of_ne_zero hzero
            let coordinate : Fin q :=
              ⟨token.toNat - 1, by omega⟩
            match decodeTree q fuel rest with
            | none => none
            | some (lower, afterLower) =>
                match decodeTree q fuel afterLower with
                | none => none
                | some (upper, afterUpper) =>
                    some (.split coordinate lower upper, afterUpper)
      else none

/-- Parse exactly `rootCount` preorder trees. -/
def decodeForest (q fuel : ℕ) : ℕ → List UInt8 →
    Option (List (Tree q) × List UInt8)
  | 0, tokens => some ([], tokens)
  | rootCount + 1, tokens =>
      match decodeTree q fuel tokens with
      | none => none
      | some (tree, afterTree) =>
          match decodeForest q fuel rootCount afterTree with
          | none => none
          | some (trees, rest) => some (tree :: trees, rest)

/-- A successful fixed-root-count parse returns exactly that many trees. -/
theorem decodeForest_length {q fuel rootCount : ℕ} {tokens rest : List UInt8}
    {trees : List (Tree q)}
    (hdecode : decodeForest q fuel rootCount tokens = some (trees, rest)) :
    trees.length = rootCount := by
  induction rootCount generalizing tokens trees rest with
  | zero =>
      simp only [decodeForest] at hdecode
      cases hdecode
      rfl
  | succ rootCount ih =>
      cases htree : decodeTree q fuel tokens with
      | none => simp [decodeForest, htree] at hdecode
      | some treeResult =>
          obtain ⟨tree, afterTree⟩ := treeResult
          cases hforest : decodeForest q fuel rootCount afterTree with
          | none => simp [decodeForest, htree, hforest] at hdecode
          | some forestResult =>
              obtain ⟨tail, afterForest⟩ := forestResult
              simp [decodeForest, htree, hforest] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              simp [ih hforest]

/-- Decode the current production flavor of `Z23TREE1`.

The fixed header pattern is the ASCII magic `Z23TREE1`, followed by one
dimension byte, a four-byte root count, an eight-byte node count, and then one
token per node.  The decoder additionally fixes all three metadata values to
the committed production report and requires complete token consumption.
-/
def decodeProductionForest (blob : ByteArray) : Option ProductionForest :=
  match blob.toList with
  | 90 :: 50 :: 51 :: 84 :: 82 :: 69 :: 69 :: 49 ::
      q :: r0 :: r1 :: r2 :: r3 ::
      n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: tokens =>
      if q.toNat = 6 ∧
          bigEndianNat [r0, r1, r2, r3] = productionRootCount ∧
          bigEndianNat [n0, n1, n2, n3, n4, n5, n6, n7] = productionNodeCount ∧
          tokens.length = productionNodeCount then
        match hdecode : decodeForest 6 productionNodeCount productionRootCount tokens with
        | some (trees, []) => some ⟨trees, decodeForest_length hdecode⟩
        | _ => none
      else none
  | _ => none

/-- Direct connection from a successfully decoded production topology and
kernel-checked leaf replay to the current local certificate.  The blob and
root list remain explicit: no production topology artifact is currently
committed. -/
theorem currentLocalCertificate_of_decoded_forest
    (blob : ByteArray) (decoded : ProductionForest)
    (problem : IntegerLowerBoundProblem 6) (roots : List (Box 6))
    (_hroots : roots.length = productionRootCount)
    (_hdecode : decodeProductionForest blob = some decoded)
    (bridge : ForestRealBridge problem roots CurrentGapVector fun g =>
      Weighted.beta ≤ Weighted.F6 CurrentWindow.weight g.1)
    (hcheck : Forest.check problem.leafOK decoded.1 roots = true) :
    CurrentWindow.LocalCertificate :=
  currentLocalCertificate_of_checked_forest problem roots decoded.1 bridge hcheck

end Zeta23Ext.VerifiedCertificate
