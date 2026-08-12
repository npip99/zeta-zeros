/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentCentralSelection

/-!
# Honest scaled-coordinate central assembler

This module is the integration contract for the retained-zero lane.  It uses
the actual parameter scale `P.L T`, and it does not consume the obsolete
`CompactUniformCurrentGram` seam.  An analytic producer must supply an
`EntrywiseGramData` record directly in the scaled coordinate.  If endpoint
tail control requires an interior margin, that producer must charge the
additional removed atoms in its retained matrix and deletion loss before
calling this interface.
-/

noncomputable section

open Filter Matrix Asymptotics
open scoped ComplexOrder

namespace Zeta23Ext.CurrentCentralAssembler

open Zeta23
open Zeta23Ext.CurrentAnalyticBridge
open Zeta23Ext.CurrentCentralSimple
open Zeta23Ext.CurrentCentralSelection
open Zeta23Ext.CurrentRetainedWithLoss

/-- Span error against the enlarged-window count in the correct `P.L T`
coordinate. -/
def centralScaledSpanError (Z : ZeroConfig) (P : Params) (T : ℝ) : ℝ :=
  max 0 (scaledWindowLength P T - (Z.NIprime T : ℝ))

lemma scaledWindowLength_le_NIprime_add_error
    (Z : ZeroConfig) (P : Params) (T : ℝ) :
    scaledWindowLength P T ≤
      (Z.NIprime T : ℝ) + centralScaledSpanError Z P T := by
  unfold centralScaledSpanError
  linarith [le_max_right 0 (scaledWindowLength P T - (Z.NIprime T : ℝ))]

/-! ## Optional interior compression -/

/-- Discarding an additional `deleted` retained columns, for example to
obtain an endpoint margin for the Poisson-tail estimate, costs `deleted`
positive directions and exactly `2*deleted` more count loss. -/
theorem LossyRetainedDecomposition.compressInterior
    {d r u deleted b : ℕ} {N countLoss : ℝ}
    {V : Matrix (Fin d) (Fin r) ℂ} {Q : Matrix (Fin d) (Fin d) ℂ}
    (h : LossyRetainedDecomposition b N countLoss V Q)
    (S : CentralSimpleSelection V u deleted) :
    LossyRetainedDecomposition (deleted + b) N
      (countLoss + 2 * (deleted : ℝ)) S.V
      (S.compression Q h.Q_hermitian).remainder := by
  have hsplitR : (u : ℝ) + deleted = r := by exact_mod_cast S.count_split
  exact
    { col_le := S.retained_col_le
      Q_hermitian := (S.compression Q h.Q_hermitian).remainder_hermitian
      positive_index :=
        (S.compression Q h.Q_hermitian).remainder_posIndex_le h.positive_index
      countLoss_nonneg := by
        have hd : (0 : ℝ) ≤ deleted := Nat.cast_nonneg _
        linarith [h.countLoss_nonneg]
      count_seam := by
        push_cast
        nlinarith [h.count_seam] }

/-- Interior compression preserves the represented matrix, so trace and
Frobenius bounds transfer unchanged while only the count loss increases. -/
theorem LossyMomentData.compressInterior
    {d r u deleted b : ℕ} {N R₁ R₂ countLoss : ℝ}
    {V : Matrix (Fin d) (Fin r) ℂ} {Q : Matrix (Fin d) (Fin d) ℂ}
    (h : LossyMomentData b N R₁ R₂ countLoss V Q)
    (S : CentralSimpleSelection V u deleted) :
    LossyMomentData (deleted + b) N R₁ R₂
      (countLoss + 2 * (deleted : ℝ)) S.V
      (S.compression Q h.Q_hermitian).remainder := by
  have hid := S.matrix_identity Q h.Q_hermitian
    (M := V * Vᴴ + Q) rfl
  exact
    { Zeta23Ext.CurrentCentralAssembler.LossyRetainedDecomposition.compressInterior
        h.toLossyRetainedDecomposition S with
      trace_lower := by simpa only [hid] using h.trace_lower
      frobenius_upper := by simpa only [hid] using h.frobenius_upper }

/-- One-height premises not already constructed by the canonical finite
selection.  The Gram statement is explicitly in `canonicalScaledY`, hence in
the `P.L T` scale. -/
structure CanonicalHeightPremises
    (Z : ZeroConfig) (P : Params) (T R₁ R₂ err : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P) where
  finiteWindow : CurrentWindow.FiniteWindowInputs
  hc : 0 < P.a T * P.L T ^ 2
  hL : 0 < P.L T
  retained_pos : 0 < Fintype.card (RetainedAtom Z P T hconj)
  gram : EntrywiseGramData
    (canonicalScaledY Z P T hconj retained_pos)
    (canonicalCentralSelection Z P T hconj hreal hPois hc).selection.V err
  azMoments : CentralAzMomentPremise Z P T (Z.NIprime T : ℝ) R₁ R₂
  delta_small : Current.eta * blockDelta (entryEnergyError err) ≤ Current.R

/-- Assemble the fully concrete finite retained/moment/span package.  The
only remaining numerical/analytic fields are precisely those displayed in
`CanonicalHeightPremises`. -/
def CanonicalHeightPremises.toLossyFinite
    {Z : ZeroConfig} {P : Params} {T R₁ R₂ err : ℝ}
    {hconj : ZeroSide.PhiHatConj T P}
    {hreal : ZeroSide.PhiHatReal T P} {hPois : ZeroSide.PoissonSq T P}
    (h : CanonicalHeightPremises Z P T R₁ R₂ err hconj hreal hPois) :
    let S := canonicalCentralSelection Z P T hconj hreal hPois h.hc
    LossyFiniteEntrywiseAnalyticInputs
      (P.d T) S.r (S.deleted + (Z.s2 T + Z.p T))
      (Z.NIprime T : ℝ) (centralScaledSpanError Z P T) err R₁ R₂
      (2 * (S.deleted : ℝ)) := by
  dsimp only
  let S := canonicalCentralSelection Z P T hconj hreal hPois h.hc
  have hrEq : S.r = Fintype.card (RetainedAtom Z P T hconj) := rfl
  have hV := canonicalCentralSelection_V_eq_retainedV
    Z P T hconj hreal hPois h.hc h.retained_pos
  exact
    { finiteWindow := h.finiteWindow
      r_pos := by
        change 0 < Fintype.card (RetainedAtom Z P T hconj)
        exact h.retained_pos
      N_nonneg := Nat.cast_nonneg _
      spanError_nonneg := le_max_left _ _
      y := canonicalScaledY Z P T hconj h.retained_pos
      y_strictMono := canonicalScaledY_strictMono Z P T hconj h.retained_pos h.hL
      V := S.selection.V
      Q := (S.selection.compression (concreteAllSimpleQ Z P T hconj)
        (concreteAllSimpleQ_hermitian Z P T hconj)).remainder
      gram := h.gram
      moments := canonical_lossyMomentData Z P T R₁ R₂ hconj hreal hPois
        h.hc h.azMoments
      spanControl := by
        have hspan := canonicalScaledY_span_le Z P T hconj h.retained_pos h.hL.le
        exact hspan.trans (scaledWindowLength_le_NIprime_add_error Z P T)
      delta_small := h.delta_small }

/-- A nonnegative loss bounded by twice a boundary count which is `o(N)` is
itself `o(N)`.  This packages the exact direction used for canonical deletion:
`countLoss ≤ 2*NII`, not the converse. -/
theorem deletionLossLittleO_of_boundary
    {X : Type*} {l : Filter X}
    {N boundary countLoss : X → ℝ}
    (hboundary_nonneg : ∀ᶠ x in l, 0 ≤ boundary x)
    (hloss_nonneg : ∀ᶠ x in l, 0 ≤ countLoss x)
    (hloss_le : ∀ᶠ x in l, countLoss x ≤ 2 * boundary x)
    (hboundary : boundary =o[l] N) :
    countLoss =o[l] N := by
  have hbig : countLoss =O[l] boundary :=
    IsBigO.of_bound 2 (by
      filter_upwards [hboundary_nonneg, hloss_nonneg, hloss_le] with x hb hl hle
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hb]
      exact hle)
  exact hbig.trans_isLittleO hboundary

/-- Final asymptotic assembler with the deletion premise reduced to an
explicit boundary-count domination and `boundary=o(N)`. -/
theorem target_of_boundaryLossLittleO
    {X : Type*} {l : Filter X}
    (r : X → ℕ) (N spanError err R₁ R₂ countLoss boundary : X → ℝ)
    (countLoss_nonneg : ∀ x, 0 ≤ countLoss x)
    (eventuallyAnalytic : ∀ᶠ x in l, ∃ d b : ℕ,
      Nonempty (LossyFiniteEntrywiseAnalyticInputs d (r x) b
        (N x) (spanError x) (err x) (R₁ x) (R₂ x) (countLoss x)))
    (N_eventually_nonneg : ∀ᶠ x in l, 0 ≤ N x)
    (boundary_eventually_nonneg : ∀ᶠ x in l, 0 ≤ boundary x)
    (countLoss_le_boundary : ∀ᶠ x in l,
      countLoss x ≤ 2 * boundary x)
    (baseErrorsLittleO : baseTotalError r spanError err R₁ R₂ =o[l] N)
    (boundaryLittleO : boundary =o[l] N) :
    ∀ᶠ x in l, Current.target * N x ≤ (r x : ℝ) :=
  target_of_littleO r N spanError err R₁ R₂ countLoss countLoss_nonneg
    eventuallyAnalytic N_eventually_nonneg baseErrorsLittleO
    (deletionLossLittleO_of_boundary boundary_eventually_nonneg
      (Eventually.of_forall countLoss_nonneg) countLoss_le_boundary boundaryLittleO)

end Zeta23Ext.CurrentCentralAssembler
