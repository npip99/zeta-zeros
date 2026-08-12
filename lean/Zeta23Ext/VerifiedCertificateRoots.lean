/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.VerifiedCertificateForest

/-!
# Decoder for production root-box artifacts

`Z23ROOT1` is the exact compact companion to the topology-only `Z23TREE1`
format.  It stores `q`, the root count, and then the inclusive `(lo,hi)`
endpoints as unsigned 32-bit big-endian integers.  This module specializes the
decoder to the current six-dimensional, 324-root production artifact.
-/

namespace Zeta23Ext.VerifiedCertificate

/-- Read one unsigned 32-bit big-endian integer. -/
def decodeU32 : List UInt8 → Option (ℕ × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: rest =>
      some (bigEndianNat [b0, b1, b2, b3], rest)
  | _ => none

/-- Construct a six-dimensional inclusive box from twelve endpoints. -/
def boxOfEndpoints : List ℕ → Option (Box 6)
  | [lo0, hi0, lo1, hi1, lo2, hi2, lo3, hi3, lo4, hi4, lo5, hi5] =>
      if lo0 ≤ hi0 ∧ lo1 ≤ hi1 ∧ lo2 ≤ hi2 ∧ lo3 ≤ hi3 ∧
          lo4 ≤ hi4 ∧ lo5 ≤ hi5 then
        some ⟨![lo0, lo1, lo2, lo3, lo4, lo5],
          ![hi0, hi1, hi2, hi3, hi4, hi5]⟩
      else none
  | _ => none

/-- Read exactly `endpointCount` unsigned endpoints. -/
def decodeEndpoints : ℕ → List UInt8 → Option (List ℕ × List UInt8)
  | 0, bytes => some ([], bytes)
  | endpointCount + 1, bytes =>
      match decodeU32 bytes with
      | none => none
      | some (value, rest) =>
          match decodeEndpoints endpointCount rest with
          | none => none
          | some (values, after) => some (value :: values, after)

/-- Read one current six-dimensional box. -/
def decodeBox6 (bytes : List UInt8) : Option (Box 6 × List UInt8) :=
  match decodeEndpoints 12 bytes with
  | none => none
  | some (endpoints, rest) =>
      match boxOfEndpoints endpoints with
      | none => none
      | some box => some (box, rest)

/-- Read exactly `rootCount` current boxes. -/
def decodeRootBoxes : ℕ → List UInt8 → Option (List (Box 6) × List UInt8)
  | 0, bytes => some ([], bytes)
  | rootCount + 1, bytes =>
      match decodeBox6 bytes with
      | none => none
      | some (box, rest) =>
          match decodeRootBoxes rootCount rest with
          | none => none
          | some (boxes, after) => some (box :: boxes, after)

/-- Successful root decoding returns exactly the requested number of boxes. -/
theorem decodeRootBoxes_length {rootCount : ℕ} {bytes rest : List UInt8}
    {roots : List (Box 6)}
    (hdecode : decodeRootBoxes rootCount bytes = some (roots, rest)) :
    roots.length = rootCount := by
  induction rootCount generalizing bytes roots rest with
  | zero =>
      simp only [decodeRootBoxes] at hdecode
      cases hdecode
      rfl
  | succ rootCount ih =>
      cases hbox : decodeBox6 bytes with
      | none => simp [decodeRootBoxes, hbox] at hdecode
      | some boxResult =>
          obtain ⟨box, afterBox⟩ := boxResult
          cases htail : decodeRootBoxes rootCount afterBox with
          | none => simp [decodeRootBoxes, hbox, htail] at hdecode
          | some tailResult =>
              obtain ⟨tail, afterTail⟩ := tailResult
              simp [decodeRootBoxes, hbox, htail] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              simp [ih htail]

/-- A decoded production root artifact carries its checked root count. -/
def ProductionRoots :=
  {roots : List (Box 6) // roots.length = productionRootCount}

/-- Decode the current production flavor of `Z23ROOT1`. -/
def decodeProductionRoots (blob : ByteArray) : Option ProductionRoots :=
  match blob.toList with
  | 90 :: 50 :: 51 :: 82 :: 79 :: 79 :: 84 :: 49 ::
      q :: r0 :: r1 :: r2 :: r3 :: bytes =>
      if q.toNat = 6 ∧
          bigEndianNat [r0, r1, r2, r3] = productionRootCount ∧
          bytes.length = productionRootCount * 6 * 8 then
        match hdecode : decodeRootBoxes productionRootCount bytes with
        | some (roots, []) => some ⟨roots, decodeRootBoxes_length hdecode⟩
        | _ => none
      else none
  | _ => none

/-- Decoded root bytes and decoded topology bytes feed the existing checked
forest theorem without any separately trusted transcription of root boxes. -/
theorem currentLocalCertificate_of_decoded_artifacts
    (treeBlob rootBlob : ByteArray)
    (trees : ProductionForest) (roots : ProductionRoots)
    (problem : IntegerLowerBoundProblem 6)
    (_htrees : decodeProductionForest treeBlob = some trees)
    (_hroots : decodeProductionRoots rootBlob = some roots)
    (bridge : ForestRealBridge problem roots.1 CurrentGapVector fun g =>
      Weighted.beta ≤ Weighted.F6 CurrentWindow.weight g.1)
    (hcheck : Forest.check problem.leafOK trees.1 roots.1 = true) :
    CurrentWindow.LocalCertificate :=
  currentLocalCertificate_of_checked_forest problem roots.1 trees.1 bridge hcheck

end Zeta23Ext.VerifiedCertificate
