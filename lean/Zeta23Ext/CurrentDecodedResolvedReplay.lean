/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentTangentPayloadDecoder
import Zeta23Ext.CurrentResolvedAnnotatedReplay

/-!
# Decoder bridge for compact resolved tangent replay

This is the artifact-facing composition point.  The tangent payload bytes are
strictly decoded into the compact RMQ-backed table; annotated topology IDs are
resolved through that same table and the same-ID center-data resolver; and the
global curvature sparse table is checked exactly once before replay.
-/

noncomputable section

namespace Zeta23Ext.VerifiedCertificate.CurrentDecodedResolvedReplay

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay
open Zeta23Ext.VerifiedCertificate.CurrentTangent
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CurvatureRMQ
open Zeta23Ext.VerifiedCertificate.CurrentTangent.PayloadDecoder

abbrev ResolvedCertificate (table : SparseTable) :=
  Zeta23Ext.VerifiedCertificate.CurrentTangent.Resolved.Certificate table

abbrev ResolvedProductionForest (table : SparseTable) :=
  Zeta23Ext.VerifiedCertificate.AnnotatedDecoder.ProductionForest
    (ResolvedCertificate table)

/-- Successful decoding of both artifacts, followed by the exact replay
check, yields the remaining current-window local certificate.  The payload
decode premise is the provenance link from `payloads` to the fully consumed
`Z23TAN1` bytes; the topology decoder itself resolves through `payloads`, so
it cannot substitute a different compact certificate table. -/
theorem currentLocalCertificate_of_decoded_artifacts
    (curvature : SparseTable) (hCurvature : curvature.check = true)
    (resolveRange : ℕ → Option CompactRange.Evidence)
    (payloadBlob : ByteArray) (payloads : PayloadTable)
    (_hPayload : decodeProductionPayloads resolveRange payloadBlob = some payloads)
    (resolveCenter : ℕ → Option
      (CompactValueGradient.Witness curvature.cells))
    (forestBlob : ByteArray) (forest : ResolvedProductionForest curvature)
    (hForest :
      AnnotatedDecoder.decodeProductionForest
        (payloads.resolveResolved curvature resolveCenter) forestBlob = some forest)
    (data : CurrentReplay.RangeKernelTable) (roots : List (Box 6))
    (hgrid : data.table.grid = 4000)
    (hKernel : data.table.Sound CurrentWindow.weight)
    (initial : CurrentReplay.InitialRootEvidence data roots)
    (hcheck : Annotated.Forest.check (CurrentReplay.problem data).leafOK
      (CurrentResolvedAnnotatedReplay.tangentOK curvature) forest.1 roots = true) :
    CurrentWindow.LocalCertificate :=
  CurrentResolvedAnnotatedReplay.currentLocalCertificate_of_decoded_resolved_replay
    curvature hCurvature (payloads.resolveResolved curvature resolveCenter)
      forestBlob forest hForest data roots hgrid hKernel initial hcheck

end Zeta23Ext.VerifiedCertificate.CurrentDecodedResolvedReplay

end
