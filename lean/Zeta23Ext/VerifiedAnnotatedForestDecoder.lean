/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentAnnotatedReplay
import Zeta23Ext.VerifiedCertificateForest

/-!
# Decoder for leaf-tagged production forests

`Z23ANN1` is the heterogeneous companion to `Z23TREE1`.  Every node starts
with one tag byte: `0` is a regular leaf, `1` is a tangent leaf followed by an
unsigned 64-bit payload index, and `2,...,q+1` are split coordinates.  A
caller-supplied resolver turns an accepted payload index into the actual
checked evidence value.

The production decoder verifies the dimension, root count, node count,
tangent-leaf count, complete input consumption, and successful resolution of
every tangent payload index.  It does not parse the separate payload artifact;
that format remains an independent finite-data layer.
-/

namespace Zeta23Ext.VerifiedCertificate.AnnotatedDecoder

open Zeta23Ext.VerifiedCertificate
def productionTangentLeafCount : ℕ := 406186

/-- Read an unsigned 64-bit big-endian integer. -/
def decodeU64 : List UInt8 → Option (ℕ × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      some (bigEndianNat [b0, b1, b2, b3, b4, b5, b6, b7], rest)
  | _ => none

/-- Decoded tree, unconsumed bytes, node count, and tangent-leaf count. -/
abbrev TreeResult (q : ℕ) (Evidence : Type*) :=
  Annotated.Tree q Evidence × List UInt8 × ℕ × ℕ

/-- Parse one annotated preorder tree. -/
def decodeTree {Evidence : Type*} (resolve : ℕ → Option Evidence)
    (q fuel : ℕ) : List UInt8 → Option (TreeResult q Evidence)
  | [] => none
  | token :: rest =>
      if hregular : token.toNat = 0 then
        some (.leaf .regular, rest, 1, 0)
      else if htangent : token.toNat = 1 then
        match decodeU64 rest with
        | none => none
        | some (payload, afterPayload) =>
            match resolve payload with
            | none => none
            | some evidence =>
                some (.leaf (.tangent evidence), afterPayload, 1, 1)
      else if hsplit : token.toNat ≤ q + 1 then
        match fuel with
        | 0 => none
        | fuel + 1 =>
            have hcoord : token.toNat - 2 < q := by omega
            let coordinate : Fin q := ⟨token.toNat - 2, hcoord⟩
            match decodeTree resolve q fuel rest with
            | none => none
            | some (lower, afterLower, lowerNodes, lowerTangents) =>
                match decodeTree resolve q fuel afterLower with
                | none => none
                | some (upper, afterUpper, upperNodes, upperTangents) =>
                    some (.split coordinate lower upper, afterUpper,
                      1 + lowerNodes + upperNodes,
                      lowerTangents + upperTangents)
      else none

/-- Decoded forest, unconsumed bytes, node count, and tangent-leaf count. -/
abbrev ForestResult (q : ℕ) (Evidence : Type*) :=
  List (Annotated.Tree q Evidence) × List UInt8 × ℕ × ℕ

/-- Parse exactly `rootCount` annotated trees. -/
def decodeForest {Evidence : Type*} (resolve : ℕ → Option Evidence)
    (q fuel : ℕ) : ℕ → List UInt8 → Option (ForestResult q Evidence)
  | 0, bytes => some ([], bytes, 0, 0)
  | rootCount + 1, bytes =>
      match decodeTree resolve q fuel bytes with
      | none => none
      | some (tree, afterTree, treeNodes, treeTangents) =>
          match decodeForest resolve q fuel rootCount afterTree with
          | none => none
          | some (trees, rest, forestNodes, forestTangents) =>
              some (tree :: trees, rest, treeNodes + forestNodes,
                treeTangents + forestTangents)

theorem decodeForest_length {Evidence : Type*}
    {resolve : ℕ → Option Evidence} {q fuel rootCount : ℕ}
    {bytes rest : List UInt8} {trees : List (Annotated.Tree q Evidence)}
    {nodes tangents : ℕ}
    (hdecode : decodeForest resolve q fuel rootCount bytes =
      some (trees, rest, nodes, tangents)) :
    trees.length = rootCount := by
  induction rootCount generalizing bytes trees rest nodes tangents with
  | zero =>
      simp only [decodeForest] at hdecode
      cases hdecode
      rfl
  | succ rootCount ih =>
      cases htree : decodeTree resolve q fuel bytes with
      | none => simp [decodeForest, htree] at hdecode
      | some treeResult =>
          obtain ⟨tree, afterTree, treeNodes, treeTangents⟩ := treeResult
          cases hforest : decodeForest resolve q fuel rootCount afterTree with
          | none => simp [decodeForest, htree, hforest] at hdecode
          | some forestResult =>
              obtain ⟨tail, afterForest, forestNodes, forestTangents⟩ :=
                forestResult
              simp [decodeForest, htree, hforest] at hdecode
              rcases hdecode with ⟨rfl, rfl, rfl, rfl⟩
              simp [ih hforest]

def ProductionForest (Evidence : Type*) :=
  {trees : List (Annotated.Tree 6 Evidence) // trees.length = productionRootCount}

/-- Strict decoder for the current production `Z23ANN1` header and body. -/
def decodeProductionForest {Evidence : Type*}
    (resolve : ℕ → Option Evidence) (blob : ByteArray) :
    Option (ProductionForest Evidence) :=
  match blob.toList with
  | 90 :: 50 :: 51 :: 65 :: 78 :: 78 :: 49 ::
      q :: r0 :: r1 :: r2 :: r3 ::
      n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 ::
      t0 :: t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: t7 :: bytes =>
      if q.toNat = 6 ∧
          bigEndianNat [r0, r1, r2, r3] = productionRootCount ∧
          bigEndianNat [n0, n1, n2, n3, n4, n5, n6, n7] =
            productionNodeCount ∧
          bigEndianNat [t0, t1, t2, t3, t4, t5, t6, t7] =
            productionTangentLeafCount then
        match hdecode : decodeForest resolve 6 productionNodeCount
            productionRootCount bytes with
        | some (trees, [], nodes, tangents) =>
            if nodes = productionNodeCount ∧
                tangents = productionTangentLeafCount then
              some ⟨trees, decodeForest_length hdecode⟩
            else none
        | _ => none
      else none
  | _ => none

/-- Successfully decoded annotated bytes can be replayed without a separate
trusted transcription of the tree topology. -/
theorem currentLocalCertificate_of_decoded_annotated_replay
    (resolve : ℕ → Option CurrentTangent.Local.Certificate)
    (blob : ByteArray) (decoded : ProductionForest CurrentTangent.Local.Certificate)
    (data : CurrentReplay.RangeKernelTable) (roots : List (Box 6))
    (_hdecode : decodeProductionForest resolve blob = some decoded)
    (hgrid : data.table.grid = 4000)
    (htable : data.table.Sound CurrentWindow.weight)
    (initial : CurrentReplay.InitialRootEvidence data roots)
    (producer : ∀ (c : CurrentTangent.Local.Certificate) (box : Box 6),
      c.check box = true → CurrentTangent.CurrentSemantics.ProducerInputs c box)
    (hcheck : Annotated.Forest.check (CurrentReplay.problem data).leafOK
      CurrentTangent.Local.certificateTangentOK decoded.1 roots = true) :
    CurrentWindow.LocalCertificate :=
  CurrentAnnotatedReplay.currentLocalCertificate_of_producer_replay
    data roots hgrid htable initial producer decoded.1 hcheck

end Zeta23Ext.VerifiedCertificate.AnnotatedDecoder
