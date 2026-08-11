/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowInterface

/-!
# Bridge from the recorded Arb reports to the current Lean interfaces

The two report files are embedded at compile time.  Lean checks that the
embedded summaries name the exact target, grid, node count, and table hashes
used by the paper, and it checks that the rational parameters transcribed into
Lean agree with the current-window definitions.

What Lean cannot infer from a successful text report is the semantic
soundness of the Python/Arb verifier.  The two implications in
`ExternalVerifierSoundness` are therefore explicit inputs.  This is the
smallest honest trust boundary: from those implications and the kernel-checked
acceptance of the embedded reports, Lean constructs exactly
`CurrentWindow.FiniteWindowInputs`.
-/

noncomputable section
set_option maxRecDepth 100000

namespace Zeta23Ext.CertificateBridge

open Zeta23Ext
open Zeta23Ext.CurrentWindow

/-! ## Reports embedded in the Lean build -/

/-- The committed summary of the exhaustive `F ≥ 509/100000` search. -/
def mainReport : String :=
  include_str "../../certificates/weighted-p1-eps509-100000-grid4000.txt"

/-- The committed summary of the window and endgame Arb checks. -/
def fastReport : String :=
  include_str "../../certificates/fast-parts-eps509.txt"

/-- Exact expected contents of the committed main-report artifact. -/
def expectedMainReport : String :=
  "verified=True\n" ++
  "target=F >= 509/100000\n" ++
  "grid=4000\n" ++
  "nodes=1739356\n" ++
  "pruned=869840\n" ++
  "splits=869516\n" ++
  "maximum_depth=57\n" ++
  "initial_boxes=324\n" ++
  "elapsed_seconds=617.591\n" ++
  "cutoff_cells=46830\n" ++
  "interval_pruned=456833\n" ++
  "pressure_pruned=6821\n" ++
  "tangent_pruned=406186\n" ++
  "w_second_table_sha256=201f4fab9b2b83f42f266251c8a21fd641af44c0a35144156f5c36577fca79a5\n" ++
  "w_table_sha256=1a015aa20ce6457a7dc233344f953a5b4144e5a4915284b7354fc6f5e070de95\n" ++
  "workers=6\n" ++
  "wall_seconds=617.6\n"

/-- Exact expected contents of the committed fast-report artifact. -/
def expectedFastReport : String :=
  "min v >= [0.750213217018232 +/- 2.12e-16]  [>= 3/4: True]\n" ++
  "max v <= [0.995632902191690 +/- 1.72e-16]  [<= 1: True]\n" ++
  "monotone on [0,1/2]: v'' near 0 <= [-0.853818724613 +/- 5.57e-14], " ++
    "v' away <= [-5.69610399415e-6 +/- 4.71e-18]  [certified: True]\n" ++
  "c1(v) = [0.75327129230193469930 +/- 3.47e-21]\n" ++
  "H(v)  = [0.67245704141454428878 +/- 4.25e-21]  [>= 672457/1000000: True]\n" ++
  "A = [1.241960000 +/- 3e-14]  R = [1.22886518210501014 +/- 3.06e-18]\n" ++
  "final bound = [0.6731951989015205755077 +/- 3.81e-23]  [>= 134639/200000: True]\n" ++
  "fast_parts_verified=True\n"

/-- Syntactic acceptance predicate for the committed main report.

This deliberately says only what occurs in the embedded report.  It is not a
claim about the mathematical soundness of the program that produced it.
-/
abbrev MainReportAccepted : Prop :=
  mainReport = expectedMainReport

/-- Syntactic acceptance predicate for the committed fast report. -/
abbrev FastReportAccepted : Prop :=
  fastReport = expectedFastReport

/-- Lean verifies the metadata in the exact main report embedded above. -/
theorem mainReportAccepted : MainReportAccepted := by
  rfl

/-- Lean verifies the claims printed in the exact fast report embedded above. -/
theorem fastReportAccepted : FastReportAccepted := by
  rfl

/-! ## Exact rational parameter alignment -/

/-- Signed coefficient numerator recorded by the Python design, with common
denominator `10^9`. -/
def windowNumerator (j : Fin 7) : ℤ :=
  match (j : ℕ) with
  | 0 => 1000000000
  | 1 => 3322500
  | 2 => -7609135
  | 3 => 1190194
  | 4 => -731476
  | 5 => -1680572
  | 6 => 1141360
  | _ => 0

/-- The cosine coefficients in the Lean kernel are exactly the signed
`design.py` numerators divided by `10^9`. -/
theorem coefficient_eq_recorded (j : Fin 7) :
    CurrentWindow.coefficient j = (windowNumerator j : ℝ) / 1000000000 := by
  fin_cases j <;> norm_num [CurrentWindow.coefficient, windowNumerator]

/-- The local target in the report is exactly the Lean weighted target. -/
theorem localTarget_eq_recorded :
    Weighted.beta = (509 : ℝ) / 100000 := by
  rfl

/-- The pressure in the report design is exactly the Lean pressure. -/
theorem pressure_eq_recorded :
    Weighted.pressure = (1 : ℝ) / 2300 := by
  rfl

/-- The current block size used by the deduction is the recorded `250`. -/
theorem blockLength_eq_recorded : Weighted.blockLength = 250 := by
  rfl

/-- The exact weighted table has the paper's capacity two at every span. -/
theorem recorded_span_capacity {r : ℕ} (hr1 : 1 ≤ r) (hr6 : r ≤ 6) :
    ∑ i ∈ Finset.range (7 - r), Weighted.pairWeight i (i + r) = 2 :=
  Weighted.pairWeight_capacity hr1 hr6

/-- The analytic lower endpoint in the fast report is exactly the endpoint in
the Lean window interface. -/
theorem Hcert_eq_recorded : CurrentWindow.Hcert = (672457 : ℝ) / 1000000 := by
  rfl

/-! ## Explicit semantic trust boundary -/

/-- The two facts that a formal verification of the Python/Arb checkers would
have to prove.  No value of this structure is manufactured in this module. -/
structure ExternalVerifierSoundness : Prop where
  main : MainReportAccepted → CurrentWindow.LocalCertificate
  fast : FastReportAccepted → CurrentWindow.WindowCertificate

/-- Once verifier soundness is supplied, the embedded accepted reports yield
exactly the two finite inputs consumed by the current Lean development. -/
theorem finiteWindowInputs_of_externalSoundness
    (hsound : ExternalVerifierSoundness) : CurrentWindow.FiniteWindowInputs :=
  ⟨hsound.main mainReportAccepted, hsound.fast fastReportAccepted⟩

/-- Equivalent unbundled form, convenient for downstream theorem statements. -/
theorem finiteWindowInputs_of_report_implications
    (hmain : MainReportAccepted → CurrentWindow.LocalCertificate)
    (hfast : FastReportAccepted → CurrentWindow.WindowCertificate) :
    CurrentWindow.FiniteWindowInputs :=
  finiteWindowInputs_of_externalSoundness ⟨hmain, hfast⟩

end Zeta23Ext.CertificateBridge
