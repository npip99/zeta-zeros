/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentInteriorRetentionBridge

/-!
# Eventual analytic package for the ordered interior compression

All retained data in this file are constructed at one height, after a proof
that the interior cardinality is positive has been supplied.  The eventual
theorems quantify over such a proof; they do not require data or fabricate
zeros at exceptional heights where the cardinality may vanish.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Filter Matrix Finset Set Asymptotics
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentInteriorAnalyticPackage

open Zeta23
open Zeta23.ZeroSide
open Zeta23Ext.CurrentAnalyticBridge
open Zeta23Ext.CurrentAnalyticInstantiation
open Zeta23Ext.CurrentCompactGram
open Zeta23Ext.CurrentInfiniteKernel
open Zeta23Ext.CurrentCentralSimple
open Zeta23Ext.CurrentCentralSelection
open Zeta23Ext.CurrentCentralAssembler
open Zeta23Ext.CurrentRetainedWithLoss
open Zeta23Ext.CurrentInteriorRetention
open Zeta23Ext.CurrentInteriorRetentionBridge

/-- The explicit one-height error: endpoint lattice tails plus the global
infinite-kernel approximation. -/
def currentInteriorGramError (P : Params) (T : ℝ) : ℝ :=
  rhoMarginError (marginScale P T) + infiniteKernelError P T

theorem tendsto_currentInteriorGramError {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    Tendsto (currentInteriorGramError P) atTop (nhds 0) := by
  change Tendsto (fun T => rhoMarginError (marginScale P T) +
    infiniteKernelError P T) atTop (nhds 0)
  simpa only [add_zero] using
    (tendsto_rhoMarginError_marginScale hP).add
      (tendsto_infiniteKernelError hP hcert)

lemma rhoMarginError_nonneg {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ rhoMarginError q := by
  unfold rhoMarginError
  positivity

/-- One-height retained data for the actual current parameters. -/
abbrev CurrentInteriorData (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hr : 0 < Fintype.card
      (InteriorIndex Z (P.atV CurrentWindow.window T) T
        ZeroSide.phiHatConj)) :=
  interiorRetainedZeroData Z (P.atV CurrentWindow.window T) T
    ZeroSide.phiHatConj hr

/-- Eventually, every positive-cardinality interior compression has an
ordinary entrywise Gram record with an explicit vanishing error.  Positivity
is local and universally quantified inside the eventual statement. -/
theorem eventually_currentInterior_entrywiseGramData
    {Z : ZeroConfig} {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    ∀ᶠ T in atTop,
      0 ≤ currentInteriorGramError P T ∧
      ∀ hr : 0 < Fintype.card
          (InteriorIndex Z (P.atV CurrentWindow.window T) T
            ZeroSide.phiHatConj),
        EntrywiseGramData
          (scaledY (CurrentInteriorData Z P T hr)
            (P.atV CurrentWindow.window T))
          ((CurrentInteriorData Z P T hr).V
            (P.atV CurrentWindow.window T))
          (currentInteriorGramError P T) := by
  have htail := eventually_current_interior_rho_tail (Z := Z) hP hcert
  have hinf := (uniformly_normalizedInfiniteKernel_current hP hcert).2
  have hlocal := CurrentCompactGram.eventually_currentLocalHypsCore hP hcert
  filter_upwards [htail, hinf, hlocal, Params.eventually_w8 hP] with
      T htailT hinfT hlocalT h8
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hW := CurrentWindowAdmissibility.admWindow_current hP hcert h8
  have haHalf := current_a_half hP hcert h8 hW
  have ha : 0 < (P.atV CurrentWindow.window T).a T := by linarith
  have hc : 0 < (P.atV CurrentWindow.window T).a T *
      (P.atV CurrentWindow.window T).L T ^ 2 := by
    simp only [Params.atV_L]
    positivity
  have hPhiEven : ∀ x : ℝ,
      (P.atV CurrentWindow.window T).PhiR T (-x) =
        (P.atV CurrentWindow.window T).PhiR T x := by
    intro x
    change (((P.atV CurrentWindow.window T).localFun T).Phi (-x)) =
      (((P.atV CurrentWindow.window T).localFun T).Phi x)
    rw [Params.atV_localFun T hP CurrentWindow.window_even]
    exact hW.VPhiR_even x
  constructor
  · exact add_nonneg (rhoMarginError_nonneg (Real.sqrt_nonneg _)) hinfT.1
  · intro hr
    let Q := P.atV CurrentWindow.window T
    let ret := CurrentInteriorData Z P T hr
    refine
      { windowFacts := hcert
        err_nonneg := by
          change 0 ≤ rhoMarginError (marginScale P T) + infiniteKernelError P T
          exact add_nonneg
            (rhoMarginError_nonneg (Real.sqrt_nonneg _)) hinfT.1
        close := ?_ }
    intro i j _hij _hdist
    have hfinite := norm_gramEntry_sub_normalizedInfiniteKernel_le
      ret ZeroSide.phiHatReal hc hPhiEven hlocalT i j
    have hinfinite := hinfT.2
      (scaledY ret Q j - scaledY ret Q i)
    have hden : 0 < Q.a T * Q.L T ^ 2 := hc
    have hi := htailT (orderedInteriorEquiv Z Q T ZeroSide.phiHatConj i)
    have hj := htailT (orderedInteriorEquiv Z Q T ZeroSide.phiHatConj j)
    have hi' :
        PrimeSide.rho (Q.toSetting T) (Q.localFun T) (ordinate ret i) /
            (Q.a T * Q.L T ^ 2) ≤ rhoMarginError (marginScale P T) := by
      simpa [Q, ret, CurrentInteriorData, interiorRetainedZeroData,
        CurrentCompactGram.ordinate] using hi
    have hj' :
        PrimeSide.rho (Q.toSetting T) (Q.localFun T) (ordinate ret j) /
            (Q.a T * Q.L T ^ 2) ≤ rhoMarginError (marginScale P T) := by
      simpa [Q, ret, CurrentInteriorData, interiorRetainedZeroData,
        CurrentCompactGram.ordinate] using hj
    have htailBound :
        (PrimeSide.rho (Q.toSetting T) (Q.localFun T) (ordinate ret i) +
            PrimeSide.rho (Q.toSetting T) (Q.localFun T) (ordinate ret j)) /
          (2 * (Q.a T * Q.L T ^ 2)) ≤
            rhoMarginError (marginScale P T) := by
      rw [show
        (PrimeSide.rho (Q.toSetting T) (Q.localFun T) (ordinate ret i) +
            PrimeSide.rho (Q.toSetting T) (Q.localFun T) (ordinate ret j)) /
              (2 * (Q.a T * Q.L T ^ 2)) =
          ((PrimeSide.rho (Q.toSetting T) (Q.localFun T) (ordinate ret i) /
              (Q.a T * Q.L T ^ 2)) +
            (PrimeSide.rho (Q.toSetting T) (Q.localFun T) (ordinate ret j) /
              (Q.a T * Q.L T ^ 2))) / 2 by field_simp]
      linarith
    calc
      ‖((ret.V Q)ᴴ * ret.V Q) i j -
          (CurrentWindow.normalizedKernel (scaledY ret Q j - scaledY ret Q i) : ℂ)‖
          ≤ ‖((ret.V Q)ᴴ * ret.V Q) i j -
                (normalizedInfiniteKernel Q T
                  (scaledY ret Q j - scaledY ret Q i) : ℂ)‖ +
              ‖(normalizedInfiniteKernel Q T
                  (scaledY ret Q j - scaledY ret Q i) : ℂ) -
                (CurrentWindow.normalizedKernel
                  (scaledY ret Q j - scaledY ret Q i) : ℂ)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ rhoMarginError (marginScale P T) + infiniteKernelError P T := by
        gcongr
        · exact hfinite.trans htailBound
        · simpa only [← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs] using hinfinite

/-! ## One-height assembler package -/

/-- Premises not supplied automatically by the interior selection and Gram
theorem.  In particular `interior_pos` is a one-height premise, not an
eventual assertion about simple zeros. -/
structure InteriorHeightPremises
    (Z : ZeroConfig) (P : Params) (T R₁ R₂ err : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P) where
  finiteWindow : CurrentWindow.FiniteWindowInputs
  hc : 0 < P.a T * P.L T ^ 2
  hL : 0 < P.L T
  interior_pos : 0 < Fintype.card (InteriorIndex Z P T hconj)
  gram : EntrywiseGramData
    (scaledY (interiorRetainedZeroData Z P T hconj interior_pos) P)
    ((interiorRetainedZeroData Z P T hconj interior_pos).V P)
    err
  azMoments : CentralAzMomentPremise Z P T (Z.NIprime T : ℝ) R₁ R₂
  delta_small : Current.eta *
    blockDelta (entryEnergyError err) ≤ Current.R

/-- Exact deletion loss after central selection and the additional interior
compression. -/
def interiorCountLoss
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) : ℝ :=
  2 * ((canonicalCentralSelection Z P T hconj hreal hPois hc).deleted : ℝ) +
    2 * (Fintype.card (EndpointIndex Z P T hconj) : ℝ)

/-- The honest finite package after ordered interior compression. -/
def InteriorHeightPremises.toLossyFinite
    {Z : ZeroConfig} {P : Params} {T R₁ R₂ err : ℝ}
    {hconj : ZeroSide.PhiHatConj T P}
    {hreal : ZeroSide.PhiHatReal T P} {hPois : ZeroSide.PoissonSq T P}
    (h : InteriorHeightPremises Z P T R₁ R₂ err hconj hreal hPois) :
    let S0 := canonicalCentralSelection Z P T hconj hreal hPois h.hc
    let SI := orderedCanonicalInteriorCompression Z P T hconj hreal hPois h.hc
    LossyFiniteEntrywiseAnalyticInputs
      (P.d T) (Fintype.card (InteriorIndex Z P T hconj))
      (Fintype.card (EndpointIndex Z P T hconj) +
        (S0.deleted + (Z.s2 T + Z.p T)))
      (Z.NIprime T : ℝ) (centralScaledSpanError Z P T)
      err R₁ R₂
      (interiorCountLoss Z P T hconj hreal hPois h.hc) := by
  dsimp only
  let S0 := canonicalCentralSelection Z P T hconj hreal hPois h.hc
  let SI := orderedCanonicalInteriorCompression Z P T hconj hreal hPois h.hc
  let ret := interiorRetainedZeroData Z P T hconj h.interior_pos
  have hmom0 := canonical_lossyMomentData Z P T R₁ R₂ hconj hreal hPois
    h.hc h.azMoments
  have hmom :=
    CurrentCentralAssembler.LossyMomentData.compressInterior hmom0 SI
  have hV := orderedCanonicalInteriorCompression_V_eq_retainedV
    Z P T hconj hreal hPois h.hc h.interior_pos
  refine
    { finiteWindow := h.finiteWindow
      r_pos := h.interior_pos
      N_nonneg := Nat.cast_nonneg _
      spanError_nonneg := le_max_left _ _
      y := scaledY ret P
      y_strictMono := (scaledOrdinate_strictMono h.hL).comp
        ret.ordinate_strictMono
      V := ret.V P
      Q := SI.compression
        (S0.selection.compression
          (concreteAllSimpleQ Z P T hconj)
          (concreteAllSimpleQ_hermitian Z P T hconj) |>.remainder)
        (S0.selection.compression
          (concreteAllSimpleQ Z P T hconj)
          (concreteAllSimpleQ_hermitian Z P T hconj) |>.remainder_hermitian)
        |>.remainder
      gram := h.gram
      moments := by
        rw [hV] at hmom
        simpa [interiorCountLoss, S0, SI, add_assoc] using hmom
      spanControl := by
        let last : Fin (Fintype.card (InteriorIndex Z P T hconj)) :=
          ⟨Fintype.card (InteriorIndex Z P T hconj) - 1,
            Nat.sub_lt h.interior_pos Nat.zero_lt_one⟩
        have hspan :
            scaledOrdinate P T (ordinate ret last) -
                scaledOrdinate P T (ordinate ret ⟨0, h.interior_pos⟩) ≤
              scaledWindowLength P T :=
          scaledOrdinate_sub_le_windowLength h.hL.le
            (ret.dyadic ⟨0, h.interior_pos⟩).1.le (ret.dyadic last).2
        exact hspan.trans (scaledWindowLength_le_NIprime_add_error Z P T)
      delta_small := h.delta_small }

end Zeta23Ext.CurrentInteriorAnalyticPackage
