/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentResolvedTangent

/-!
# Strict decoder for compact tangent payloads

The `Z23TAN1` format is intentionally positional and canonical.  A record
contains its dense zero-based identifier, the exact rational affine data,
twenty references into a separately checked range-evidence table, and the
exact rational `LDLᵀ` certificate.  Hessian terms and the fixed production
target are reconstructed rather than duplicated in the artifact.

An integer is encoded as a four-byte big-endian byte length followed by a
big-endian magnitude.  Zero has length zero; a positive magnitude must have
no leading zero.  A rational consists of a sign byte, a numerator integer,
and a positive denominator integer.  The decoder rejects negative zero,
non-coprime numerator/denominator pairs, oversized integers, unresolved
range references, non-dense record identifiers, count mismatches, and all
trailing bytes.
-/

namespace Zeta23Ext.VerifiedCertificate.CurrentTangent.PayloadDecoder

open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentTangent
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactRange

abbrev CompactCertificate :=
  Zeta23Ext.VerifiedCertificate.CurrentTangent.CompactRange.Certificate

def maxIntegerBytes : ℕ := 256
def productionPayloadCount : ℕ := 406186

def decodeU32 : List UInt8 → Option (ℕ × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: rest =>
      some (bigEndianNat [b0, b1, b2, b3], rest)
  | _ => none

def decodeU64 : List UInt8 → Option (ℕ × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      some (bigEndianNat [b0, b1, b2, b3, b4, b5, b6, b7], rest)
  | _ => none

def decodeBytes (count : ℕ) (bytes : List UInt8) :
    Option (List UInt8 × List UInt8) :=
  if count ≤ bytes.length then some (bytes.take count, bytes.drop count)
  else none

def canonicalMagnitude (digits : List UInt8) : Bool :=
  match digits with
  | [] => true
  | first :: _ => decide (first.toNat ≠ 0)

def decodeMagnitude (bytes : List UInt8) : Option (ℕ × List UInt8) := do
  let (count, rest) ← decodeU32 bytes
  if count ≤ maxIntegerBytes then
    let (digits, after) ← decodeBytes count rest
    if canonicalMagnitude digits then some (bigEndianNat digits, after)
    else none
  else none

/-- A unique exact-rational encoding.  The sign is `0` or `1`; zero must be
positive, and numerator/denominator must be coprime. -/
def decodeRat : List UInt8 → Option (ℚ × List UInt8)
  | sign :: rest => do
      if sign.toNat ≤ 1 then
        let (numerator, afterNumerator) ← decodeMagnitude rest
        let (denominator, afterDenominator) ← decodeMagnitude afterNumerator
        if 0 < denominator ∧ numerator.Coprime denominator ∧
            (numerator ≠ 0 ∨ sign.toNat = 0) then
          let value : ℚ := (numerator : ℚ) / denominator
          some (if sign.toNat = 0 then value else -value, afterDenominator)
        else none
      else none
  | [] => none

def decodeInterval (bytes : List UInt8) : Option (QInterval × List UInt8) := do
  let (lower, rest) ← decodeRat bytes
  let (upper, after) ← decodeRat rest
  some (⟨lower, upper⟩, after)

/-- Fixed six-vector used to avoid partial indexing in decoded data. -/
structure Six (α : Type*) where
  x0 : α
  x1 : α
  x2 : α
  x3 : α
  x4 : α
  x5 : α

def Six.get {α : Type*} (v : Six α) : Fin 6 → α
  | ⟨0, _⟩ => v.x0
  | ⟨1, _⟩ => v.x1
  | ⟨2, _⟩ => v.x2
  | ⟨3, _⟩ => v.x3
  | ⟨4, _⟩ => v.x4
  | ⟨5, _⟩ => v.x5

def decodeSix (decode : List UInt8 → Option (α × List UInt8))
    (bytes : List UInt8) : Option (Six α × List UInt8) := do
  let (x0, r0) ← decode bytes
  let (x1, r1) ← decode r0
  let (x2, r2) ← decode r1
  let (x3, r3) ← decode r2
  let (x4, r4) ← decode r3
  let (x5, r5) ← decode r4
  some (⟨x0, x1, x2, x3, x4, x5⟩, r5)

def decodeRangeRefs (resolve : ℕ → Option CompactRange.Evidence) :
    ℕ → List UInt8 → Option (List CompactRange.Evidence × List UInt8)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => do
      let (id, rest) ← decodeU64 bytes
      let evidence ← resolve id
      let (tail, after) ← decodeRangeRefs resolve count rest
      some (evidence :: tail, after)

def decodePayload (resolveRange : ℕ → Option CompactRange.Evidence)
    (bytes : List UInt8) : Option (CompactCertificate × List UInt8) := do
  let (center, r0) ← decodeSix decodeRat bytes
  let (radius, r1) ← decodeSix decodeRat r0
  let (value, r2) ← decodeInterval r1
  let (gradient, r3) ← decodeSix decodeInterval r2
  let (ranges, r4) ← decodeRangeRefs resolveRange 20 r3
  let (lowerRows, r5) ← decodeSix (decodeSix decodeRat) r4
  let (diagonal, r6) ← decodeSix decodeRat r5
  let payload : TangentPayload 6 := {
    center := center.get
    radius := radius.get
    value := value
    gradient := gradient.get
    hessianTerms := ranges.map CompactRange.termOfEvidence
    ldl := {
      lower := fun i j => (lowerRows.get i).get j
      diagonal := diagonal.get
    }
    target := 509 / 100000
  }
  some (⟨payload, ranges⟩, r6)

def decodeRecordsAux (resolveRange : ℕ → Option CompactRange.Evidence) :
    (count nextId : ℕ) → List UInt8 → List CompactCertificate →
      Option (List CompactCertificate × List UInt8)
  | 0, _, bytes, reversed => some (reversed.reverse, bytes)
  | count + 1, nextId, bytes, reversed => do
      let (id, r0) ← decodeU64 bytes
      if id = nextId then
        let (payload, r1) ← decodePayload resolveRange r0
        decodeRecordsAux resolveRange count (nextId + 1) r1
          (payload :: reversed)
      else none

def decodeRecords (resolveRange : ℕ → Option CompactRange.Evidence)
    (count nextId : ℕ) (bytes : List UInt8) :
    Option (List CompactCertificate × List UInt8) :=
  decodeRecordsAux resolveRange count nextId bytes []

private theorem decodeRecordsAux_length
    {resolveRange : ℕ → Option CompactRange.Evidence}
    {count nextId : ℕ} {bytes rest : List UInt8}
    {reversed records : List CompactCertificate}
    (h : decodeRecordsAux resolveRange count nextId bytes reversed =
      some (records, rest)) :
    records.length = count + reversed.length := by
  induction count generalizing nextId bytes reversed records rest with
  | zero =>
      simp [decodeRecordsAux] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
  | succ count ih =>
      cases hu : decodeU64 bytes with
      | none => simp [decodeRecordsAux, hu] at h
      | some decodedId =>
          obtain ⟨id, r0⟩ := decodedId
          by_cases hid : id = nextId
          · cases hp : decodePayload resolveRange r0 with
            | none => simp [decodeRecordsAux, hu, hid, hp] at h
            | some decodedPayload =>
                obtain ⟨payload, r1⟩ := decodedPayload
                cases ht : decodeRecordsAux resolveRange count (nextId + 1) r1
                    (payload :: reversed) with
                | none => simp [decodeRecordsAux, hu, hid, hp, ht] at h
                | some decodedTail =>
                    obtain ⟨tail, after⟩ := decodedTail
                    simp [decodeRecordsAux, hu, hid, hp, ht] at h
                    obtain ⟨rfl, rfl⟩ := h
                    have hlen := ih ht
                    simp at hlen ⊢
                    omega
          · simp [decodeRecordsAux, hu, hid] at h

theorem decodeRecords_length {resolveRange : ℕ → Option CompactRange.Evidence}
    {count nextId : ℕ} {bytes rest : List UInt8}
    {records : List CompactCertificate}
    (h : decodeRecords resolveRange count nextId bytes = some (records, rest)) :
    records.length = count := by
  have := decodeRecordsAux_length (reversed := []) (by
    simpa [decodeRecords] using h)
  simpa using this

structure PayloadTable where
  entries : List CompactCertificate
  length_eq : entries.length = productionPayloadCount

def PayloadTable.resolve (table : PayloadTable) (id : ℕ) :
    Option CompactCertificate :=
  table.entries[id]?

/-- Final topology resolver after the independently decoded center table is
available.  Both components are selected by the same dense payload ID, so an
annotated tangent leaf receives exactly the resolved certificate type used by
`CurrentResolvedAnnotatedReplay`. -/
def PayloadTable.resolveResolved
    (payloads : PayloadTable)
    (curvature : CurvatureRMQ.SparseTable)
    (resolveCenter : ℕ → Option
      (CompactValueGradient.Witness curvature.cells))
    (id : ℕ) : Option (Resolved.Certificate curvature) := do
  let compact ← payloads.resolve id
  let centerData ← resolveCenter id
  some ⟨compact, centerData⟩

/-- Strict production decoder.  Positional records still carry an explicit
dense ID, preventing a producer from shifting, duplicating, or omitting the
index referenced by the annotated forest. -/
def decodeProductionPayloads (resolveRange : ℕ → Option CompactRange.Evidence)
    (blob : ByteArray) : Option PayloadTable :=
  match blob.toList with
  | 90 :: 50 :: 51 :: 84 :: 65 :: 78 :: 49 ::
      q :: c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: bytes =>
      if q.toNat = 6 ∧
          bigEndianNat [c0, c1, c2, c3, c4, c5, c6, c7] =
            productionPayloadCount then
        match hdecode : decodeRecords resolveRange
            productionPayloadCount 0 bytes with
        | some (records, []) =>
            some ⟨records, decodeRecords_length hdecode⟩
        | _ => none
      else none
  | _ => none

end Zeta23Ext.VerifiedCertificate.CurrentTangent.PayloadDecoder
