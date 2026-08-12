/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentCertificateReplay
import Zeta23Ext.CurrentTangentCurrentSemantics
import Zeta23Ext.VerifiedAnnotatedForest

/-!
# Current heterogeneous production replay

This is the final structural bridge for the local seven-point certificate.
Regular leaves use the exact integer lower-score table.  Tangent leaves use
the current-objective, box-local semantic certificates.  The already checked
initial-root classification handles points outside the replayed roots.

No certificate data are postulated here: callers must supply a sound current
kernel table, exact initialization evidence, a checked annotated forest, and
the semantic constructor for every accepted tangent payload.
-/

namespace Zeta23Ext.VerifiedCertificate.CurrentAnnotatedReplay

open Zeta23Ext
open Zeta23Ext.VerifiedCertificate

/-- A checked heterogeneous production forest discharges the sole remaining
`CurrentWindow.LocalCertificate` premise.  The conclusion is the exact real
current-window objective, not an integer-score surrogate. -/
theorem currentLocalCertificate_of_annotated_replay
    (data : CurrentReplay.RangeKernelTable) (roots : List (Box 6))
    (hgrid : data.table.grid = 4000)
    (htable : data.table.Sound CurrentWindow.weight)
    (initial : CurrentReplay.InitialRootEvidence data roots)
    (semantics : ∀ (c : CurrentTangent.Local.Certificate) (box : Box 6),
      c.check box = true → CurrentTangent.Local.CurrentSemantics c box)
    (trees : List (Annotated.Tree 6 CurrentTangent.Local.Certificate))
    (hcheck : Annotated.Forest.check (CurrentReplay.problem data).leafOK
      CurrentTangent.Local.certificateTangentOK trees roots = true) :
    CurrentWindow.LocalCertificate := by
  have hall : ∀ point : CurrentGapVector,
      Weighted.beta ≤ Weighted.F6 CurrentWindow.weight point.1 :=
    Annotated.Forest.checked_sound
      (CurrentReplay.currentForestBridge data roots hgrid htable initial)
      CurrentTangent.Local.certificateTangentOK
      (fun c box hc point hbox =>
        CurrentTangent.Local.certificateTangentOK_sound semantics c box hc
          point (by simpa [CurrentReplay.currentForestBridge, hgrid] using hbox))
      trees hcheck
  intro gaps hgaps
  exact hall ⟨gaps, hgaps⟩

/-- Convenience form exposing only the four finite producer obligations for
each accepted tangent payload: center value, six gradient intervals, the
finite directional-gradient identity, and the checked-range Hessian bound.
All calculus and objective-identification fields are constructed internally. -/
theorem currentLocalCertificate_of_producer_replay
    (data : CurrentReplay.RangeKernelTable) (roots : List (Box 6))
    (hgrid : data.table.grid = 4000)
    (htable : data.table.Sound CurrentWindow.weight)
    (initial : CurrentReplay.InitialRootEvidence data roots)
    (producer : ∀ (c : CurrentTangent.Local.Certificate) (box : Box 6),
      c.check box = true → CurrentTangent.CurrentSemantics.ProducerInputs c box)
    (trees : List (Annotated.Tree 6 CurrentTangent.Local.Certificate))
    (hcheck : Annotated.Forest.check (CurrentReplay.problem data).leafOK
      CurrentTangent.Local.certificateTangentOK trees roots = true) :
    CurrentWindow.LocalCertificate := by
  exact currentLocalCertificate_of_annotated_replay data roots hgrid htable
    initial
    (fun c box hc => CurrentTangent.CurrentSemantics.ofProducerInputs c box
      (producer c box hc))
    trees hcheck

end Zeta23Ext.VerifiedCertificate.CurrentAnnotatedReplay
