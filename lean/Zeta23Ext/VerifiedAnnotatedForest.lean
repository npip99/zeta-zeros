/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.VerifiedCertificateForest

/-!
# Heterogeneous replay for regular and tangent leaves

The production forest has two mathematically different terminal rules.
Regular leaves establish the integer lower score consumed by
`IntegerLowerBoundProblem`; tangent leaves establish the final real conclusion
directly on a whole continuous box.  The latter cannot soundly be coerced into
an integer-score fact, because the existing real bridge only proves that the
integer score is a lower bound for the real objective.

This module supplies the generic checker needed by a future annotated
production artifact.  It deliberately contains no current table data and no
concrete tangent witness format.
-/

namespace Zeta23Ext.VerifiedCertificate.Annotated

open Zeta23Ext.VerifiedCertificate

/-- Terminal rule recorded at a leaf.  Tangent evidence is kept abstract so a
compact artifact may use an integer index while small regressions may use a
more descriptive type. -/
inductive LeafKind (Evidence : Type*) where
  | regular
  | tangent (evidence : Evidence)
  deriving DecidableEq

/-- A subdivision tree which retains the semantic kind of each leaf. -/
inductive Tree (q : ℕ) (Evidence : Type*) where
  | leaf (kind : LeafKind Evidence)
  | split (coordinate : Fin q) (lower upper : Tree q Evidence)

/-- Check an annotated tree while reconstructing every leaf box from its
root and midpoint splits. -/
def Tree.check {q : ℕ} {Evidence : Type*}
    (regularOK : Box q → Bool) (tangentOK : Evidence → Box q → Bool) :
    Tree q Evidence → Box q → Bool
  | .leaf .regular, box => regularOK box
  | .leaf (.tangent evidence), box => tangentOK evidence box
  | .split coordinate lower upper, box =>
      lower.check regularOK tangentOK (box.left coordinate) &&
        upper.check regularOK tangentOK (box.right coordinate)

/-- Soundness of one annotated tree is stated directly over real inputs.
Regular leaves pass through the integer score, while tangent leaves may prove
the conclusion without mentioning that score. -/
theorem Tree.check_sound {q : ℕ} {Evidence X : Type*}
    {problem : IntegerLowerBoundProblem q}
    {Conclusion : X → Prop}
    (locate : X → Fin q → ℕ)
    (transfer : ∀ x, problem.target ≤ problem.exactScore (locate x) → Conclusion x)
    (tangentOK : Evidence → Box q → Bool)
    (tangent_sound : ∀ evidence box, tangentOK evidence box = true →
      ∀ x, box.Contains (locate x) → Conclusion x) :
    ∀ (tree : Tree q Evidence) (root : Box q),
      tree.check problem.leafOK tangentOK root = true →
      ∀ x, root.Contains (locate x) → Conclusion x := by
  intro tree
  induction tree with
  | leaf kind =>
      intro root hcheck x hx
      cases kind with
      | regular =>
          simp only [Tree.check] at hcheck
          rw [IntegerLowerBoundProblem.leafOK, decide_eq_true_eq] at hcheck
          exact transfer x (hcheck.trans (problem.lowerScore_sound root (locate x) hx))
      | tangent evidence =>
          exact tangent_sound evidence root hcheck x hx
  | split coordinate lower upper ihLower ihUpper =>
      intro root hcheck x hx
      rw [Tree.check, Bool.and_eq_true] at hcheck
      rcases Box.contains_left_or_right hx coordinate with hleft | hright
      · exact ihLower (root.left coordinate) hcheck.1 x hleft
      · exact ihUpper (root.right coordinate) hcheck.2 x hright

namespace Forest

/-- Replay corresponding annotated trees and roots.  Mismatched list lengths
are rejected. -/
def check {q : ℕ} {Evidence : Type*}
    (regularOK : Box q → Bool) (tangentOK : Evidence → Box q → Bool) :
    List (Tree q Evidence) → List (Box q) → Bool
  | [], [] => true
  | tree :: trees, root :: roots =>
      tree.check regularOK tangentOK root &&
        check regularOK tangentOK trees roots
  | _, _ => false

/-- Every input located in a checked root is discharged by the corresponding
regular or tangent terminal rule. -/
theorem check_sound {q : ℕ} {Evidence X : Type*}
    {problem : IntegerLowerBoundProblem q}
    {Conclusion : X → Prop}
    (locate : X → Fin q → ℕ)
    (transfer : ∀ x, problem.target ≤ problem.exactScore (locate x) → Conclusion x)
    (tangentOK : Evidence → Box q → Bool)
    (tangent_sound : ∀ evidence box, tangentOK evidence box = true →
      ∀ x, box.Contains (locate x) → Conclusion x) :
    ∀ (trees : List (Tree q Evidence)) (roots : List (Box q)),
      check problem.leafOK tangentOK trees roots = true →
      ∀ x, VerifiedCertificate.Forest.Covers roots (locate x) → Conclusion x := by
  intro trees
  induction trees with
  | nil =>
      intro roots hcheck x hcover
      cases roots with
      | nil => simp [VerifiedCertificate.Forest.Covers] at hcover
      | cons root roots => simp [check] at hcheck
  | cons tree trees ih =>
      intro roots hcheck x hcover
      cases roots with
      | nil => simp [check] at hcheck
      | cons root roots =>
          rw [check, Bool.and_eq_true] at hcheck
          rcases hcover with ⟨covered, hmem, hx⟩
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | htail
          · rw [heq] at hx
            exact Tree.check_sound locate transfer tangentOK tangent_sound
              tree root hcheck.1 x hx
          · exact ih roots hcheck.2 x ⟨covered, htail, hx⟩

/-- An annotated checked forest plugs into the existing initialization bridge.
The bridge's outside-root conclusion and regular-score transfer are reused
unchanged; only tangent leaves receive the additional direct soundness rule. -/
theorem checked_sound {q : ℕ} {Evidence X : Type*}
    {problem : IntegerLowerBoundProblem q}
    {roots : List (Box q)} {Conclusion : X → Prop}
    (bridge : ForestRealBridge problem roots X Conclusion)
    (tangentOK : Evidence → Box q → Bool)
    (tangent_sound : ∀ evidence box, tangentOK evidence box = true →
      ∀ x, box.Contains (bridge.locate x) → Conclusion x)
    (trees : List (Tree q Evidence))
    (hcheck : check problem.leafOK tangentOK trees roots = true) :
    ∀ x, Conclusion x := by
  intro x
  rcases bridge.classify x with hconclusion | hcovered
  · exact hconclusion
  · exact check_sound bridge.locate bridge.transfer tangentOK tangent_sound
      trees roots hcheck x hcovered

end Forest

/-! ## Small mixed-leaf regression -/

namespace Demo

def tangentOK (_ : Unit) (box : Box 1) : Bool :=
  decide (box.hi 0 < 4)

theorem tangentOK_sound (evidence : Unit) (box : Box 1)
    (hcheck : tangentOK evidence box = true) :
    ∀ point : Fin 1 → ℕ, box.Contains point →
      VerifiedCertificate.Demo.problem.target ≤
        VerifiedCertificate.Demo.problem.exactScore point := by
  intro point hpoint
  rw [tangentOK, decide_eq_true_eq] at hcheck
  unfold VerifiedCertificate.Demo.problem VerifiedCertificate.Demo.exactScore
  simp only
  split_ifs with hlt
  · norm_num
  · have := (hpoint 0).2
    omega

/-- This tree deliberately contains one ordinary integer leaf and one direct
tangent leaf. -/
def mixedTree : Tree 1 Unit :=
  .split 0 (.split 0 (.leaf .regular) (.leaf .regular))
    (.leaf (.tangent ()))

example : mixedTree.check VerifiedCertificate.Demo.problem.leafOK tangentOK
    VerifiedCertificate.Demo.root = true := by decide

theorem mixedTree_sound (point : Fin 1 → ℕ)
    (hpoint : VerifiedCertificate.Demo.root.Contains point) :
    VerifiedCertificate.Demo.problem.target ≤
      VerifiedCertificate.Demo.problem.exactScore point := by
  apply Tree.check_sound (problem := VerifiedCertificate.Demo.problem)
    (locate := id) (transfer := fun _ h => h)
    tangentOK tangentOK_sound mixedTree VerifiedCertificate.Demo.root
  · decide
  · exact hpoint

end Demo

end Zeta23Ext.VerifiedCertificate.Annotated
