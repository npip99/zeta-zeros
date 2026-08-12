/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentResolvedTangent
import Zeta23Ext.VerifiedAnnotatedForestDecoder

/-!
# Annotated replay with resolved compact tangent evidence

This adapter specializes the heterogeneous production forest to compact,
RMQ-backed tangent certificates.  The shared sparse table is checked once at
the replay boundary.  A tangent leaf subsequently checks only its twenty
compact curvature queries, its value/gradient witness, and their exact
linkage to the replayed payload.
-/

noncomputable section

namespace Zeta23Ext.VerifiedCertificate.CurrentResolvedAnnotatedReplay

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate
open Zeta23Ext.VerifiedCertificate.CurrentReplay
open Zeta23Ext.VerifiedCertificate.CurrentTangent.CurvatureRMQ

abbrev ResolvedCertificate (table : SparseTable) :=
  Zeta23Ext.VerifiedCertificate.CurrentTangent.Resolved.Certificate table
abbrev ResolvedProductionForest (table : SparseTable) :=
  Zeta23Ext.VerifiedCertificate.AnnotatedDecoder.ProductionForest
    (ResolvedCertificate table)

/-- Per-leaf acceptance for resolved compact evidence.  The global
sparse-table check is deliberately absent from both this wrapper and
`Resolved.Certificate.check`: it is paid once by the enclosing replay
theorem. -/
noncomputable def tangentOK (table : SparseTable)
    (c : ResolvedCertificate table) (box : Box 6) : Bool :=
  c.check box

/-- Semantic soundness of one compact tangent leaf under the one-time global
sparse-table check. -/
theorem tangentOK_sound (table : SparseTable) (hTable : table.check = true)
    (c : ResolvedCertificate table) (box : Box 6)
    (hLeaf : tangentOK table c box = true) (point : CurrentGapVector)
    (hbox : box.Contains (locateGaps 4000 point)) :
    Weighted.beta ≤ Weighted.F6 CurrentWindow.weight point.1 := by
  exact Zeta23Ext.VerifiedCertificate.CurrentTangent.Resolved.sound table hTable
    c box (by simpa [tangentOK] using hLeaf) point hbox

/-- A checked heterogeneous forest of resolved compact certificates proves
the current-window local certificate.  The RMQ table is checked globally
once; regular leaves continue to use the existing exact replay bridge. -/
theorem currentLocalCertificate_of_resolved_replay
    (curvature : SparseTable) (hCurvature : curvature.check = true)
    (data : CurrentReplay.RangeKernelTable) (roots : List (Box 6))
    (hgrid : data.table.grid = 4000)
    (hKernel : data.table.Sound CurrentWindow.weight)
    (initial : CurrentReplay.InitialRootEvidence data roots)
    (trees : List (Annotated.Tree 6 (ResolvedCertificate curvature)))
    (hcheck : Annotated.Forest.check (CurrentReplay.problem data).leafOK
      (tangentOK curvature) trees roots = true) :
    CurrentWindow.LocalCertificate := by
  have hall : ∀ point : CurrentGapVector,
      Weighted.beta ≤ Weighted.F6 CurrentWindow.weight point.1 :=
    Annotated.Forest.checked_sound
      (CurrentReplay.currentForestBridge data roots hgrid hKernel initial)
      (tangentOK curvature)
      (fun c box hc point hbox =>
        tangentOK_sound curvature hCurvature c box hc point
          (by simpa [CurrentReplay.currentForestBridge, hgrid] using hbox))
      trees hcheck
  intro gaps hgaps
  exact hall ⟨gaps, hgaps⟩

/-- Decoder-facing capstone.  Successful `Z23ANN1` decoding supplies the
production forest topology and resolves each tangent payload directly to a
compact certificate; replay then yields the local theorem. -/
theorem currentLocalCertificate_of_decoded_resolved_replay
    (curvature : SparseTable) (hCurvature : curvature.check = true)
    (resolve : ℕ → Option (ResolvedCertificate curvature))
    (blob : ByteArray) (decoded : ResolvedProductionForest curvature)
    (_hdecode :
      Zeta23Ext.VerifiedCertificate.AnnotatedDecoder.decodeProductionForest
        resolve blob = some decoded)
    (data : CurrentReplay.RangeKernelTable) (roots : List (Box 6))
    (hgrid : data.table.grid = 4000)
    (hKernel : data.table.Sound CurrentWindow.weight)
    (initial : CurrentReplay.InitialRootEvidence data roots)
    (hcheck : Annotated.Forest.check (CurrentReplay.problem data).leafOK
      (tangentOK curvature) decoded.1 roots = true) :
    CurrentWindow.LocalCertificate :=
  currentLocalCertificate_of_resolved_replay curvature hCurvature data roots
    hgrid hKernel initial decoded.1 hcheck

end Zeta23Ext.VerifiedCertificate.CurrentResolvedAnnotatedReplay

end
