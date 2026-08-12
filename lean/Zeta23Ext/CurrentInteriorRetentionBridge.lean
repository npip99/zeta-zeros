/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentInteriorRetention

/-!
# Interior-retention integration bridge

This module supplies the two family-level seams deliberately left out of
`CurrentInteriorRetention`: deletion for the height-dependent current
parameters, and an ordinate-ordered reindexing of the interior columns.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Filter Matrix Finset Set Asymptotics
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentInteriorRetentionBridge

open Zeta23
open Zeta23.ZeroSide
open Zeta23Ext.CurrentCentralSimple
open Zeta23Ext.CurrentCentralSelection
open Zeta23Ext.CurrentCentralAssembler
open Zeta23Ext.CurrentAnalyticInstantiation
open Zeta23Ext.CurrentInteriorRetention

/-! ## Height-dependent endpoint deletion -/

/-- The endpoint deletion proof only uses eventual positivity and the
eventual upper bound one for the physical margin.  Consequently it applies
to a genuinely height-dependent parameter family. -/
theorem endpointDeletionFamily_isLittleO_N
    {Z : ZeroConfig} (hR : RiemannVonMangoldt Z)
    (Pf : ℝ → Params)
    (hconj : ∀ T, ZeroSide.PhiHatConj T (Pf T))
    (hpos : ∀ᶠ T in atTop, 0 < physicalMargin (Pf T) T)
    (hle : ∀ᶠ T in atTop, physicalMargin (Pf T) T ≤ 1) :
    (fun T => (Fintype.card (EndpointIndex Z (Pf T) T (hconj T)) : ℝ))
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A0, hA0, hloc⟩ := hR.local_count
  have hO : (fun T =>
      (Fintype.card (EndpointIndex Z (Pf T) T (hconj T)) : ℝ))
      =O[atTop] Real.log := by
    refine IsBigO.of_bound (4 * A0) ?_
    filter_upwards [hpos, hle, eventually_ge_atTop (4 : ℝ)] with
        T hm0 hm1 hT
    have hcard := card_endpointIndex_le_counts Z (Pf T) T (hconj T) hm0 hm1
    have hleft := hloc T
    have hright := hloc (2 * T - 1)
    have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have habsT : |T| = T := abs_of_nonneg (by linarith)
    have habs2T : |2 * T - 1| = 2 * T - 1 := abs_of_nonneg (by linarith)
    have hT3 : T + 3 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 2)]
    have h2T2 : 2 * T + 2 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 3)]
    have hlogLeft : Real.log (|T| + 3) ≤ 2 * Real.log T := by
      rw [habsT]
      calc
        Real.log (T + 3) ≤ Real.log (T ^ 2) :=
          Real.strictMonoOn_log.monotoneOn
            (show 0 < T + 3 by linarith)
            (show 0 < T ^ 2 by positivity) hT3
        _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
    have hlogRight : Real.log (|2 * T - 1| + 3) ≤ 2 * Real.log T := by
      rw [habs2T]
      calc
        Real.log (2 * T - 1 + 3) ≤ Real.log (T ^ 2) :=
          Real.strictMonoOn_log.monotoneOn
            (show 0 < 2 * T - 1 + 3 by linarith)
            (show 0 < T ^ 2 by positivity) (by linarith)
        _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hlog0]
    have hcardR :
        (Fintype.card (EndpointIndex Z (Pf T) T (hconj T)) : ℝ) ≤
          (Z.N T (T + 1) : ℝ) + (Z.N (2 * T - 1) (2 * T) : ℝ) := by
      exact_mod_cast hcard
    have hright' : (Z.N (2 * T - 1) (2 * T) : ℝ) ≤
        A0 * Real.log (|2 * T - 1| + 3) := by
      convert hright using 1 <;> ring
    have hA00 : 0 ≤ A0 := by linarith
    calc
      (Fintype.card (EndpointIndex Z (Pf T) T (hconj T)) : ℝ)
          ≤ (Z.N T (T + 1) : ℝ) +
            (Z.N (2 * T - 1) (2 * T) : ℝ) := hcardR
      _ ≤ A0 * Real.log (|T| + 3) +
          A0 * Real.log (|2 * T - 1| + 3) := add_le_add hleft hright'
      _ ≤ A0 * (2 * Real.log T) + A0 * (2 * Real.log T) := by gcongr
      _ = 4 * A0 * Real.log T := by ring
  exact hO.trans_isLittleO
    (Assembly.isLittleO_N_of_isLittleO_Tl Z hR Assembly.isLittleO_log_Tl)

lemma physicalMargin_atV_current
    (P : Params) (T : ℝ) :
    physicalMargin (P.atV CurrentWindow.window T) T = physicalMargin P T := by
  simp [physicalMargin, marginScale]

/-- The actual current-window endpoint family has deletion `o(N(T,2T))`.
Unlike the fixed-parameter theorem, its parameter argument is
`P.atV window T` at height `T`. -/
theorem currentEndpointDeletion_isLittleO_N
    {Z : ZeroConfig} {P : Params} (hP : P.Valid)
    (hR : RiemannVonMangoldt Z) :
    (fun T => (Fintype.card
        (EndpointIndex Z (P.atV CurrentWindow.window T) T
          ZeroSide.phiHatConj) : ℝ))
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  apply endpointDeletionFamily_isLittleO_N hR
    (fun T => P.atV CurrentWindow.window T) (fun _ => ZeroSide.phiHatConj)
  · filter_upwards [eventually_physicalMargin_pos hP] with T hT
    simpa only [physicalMargin_atV_current] using hT
  · filter_upwards [eventually_physicalMargin_le_one hP] with T hT
    simpa only [physicalMargin_atV_current] using hT

lemma N_isBigO_NIprime (Z : ZeroConfig) :
    (fun T => (Z.N T (2 * T) : ℝ)) =O[atTop]
      (fun T => (Z.NIprime T : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _), one_mul]
  exact_mod_cast (show Z.N T (2 * T) ≤ Z.NIprime T by
    rw [Assembly.NIprime_eq Z hT]
    exact Nat.le_add_right _ _)

/-- The current endpoint deletion is also little-o of the enlarged count
used by the central assembler. -/
theorem currentEndpointDeletion_isLittleO_NIprime
    {Z : ZeroConfig} {P : Params} (hP : P.Valid)
    (hR : RiemannVonMangoldt Z) :
    (fun T => (Fintype.card
        (EndpointIndex Z (P.atV CurrentWindow.window T) T
          ZeroSide.phiHatConj) : ℝ))
      =o[atTop] (fun T => (Z.NIprime T : ℝ)) :=
  (currentEndpointDeletion_isLittleO_N hP hR).trans_isBigO (N_isBigO_NIprime Z)

/-! ## Ordered interior reindexing -/

/-- The canonical order is inherited from the original increasing index.
This is intentionally an order isomorphism, not `Fintype.equivFin`. -/
def orderedInteriorEquiv
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fin (Fintype.card (InteriorIndex Z P T hconj)) ≃o
      InteriorIndex Z P T hconj :=
  Fintype.orderIsoFinOfCardEq _ rfl

/-- Interior first, endpoint second, with the interior summand in ordinate
order. -/
def orderedInteriorEndpointEquiv
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fin (Fintype.card (InteriorIndex Z P T hconj)) ⊕
        Fin (Fintype.card (EndpointIndex Z P T hconj)) ≃
      Fin (Fintype.card (RetainedAtom Z P T hconj)) := by
  classical
  exact (Equiv.sumCongr (orderedInteriorEquiv Z P T hconj).toEquiv
    (Fintype.equivFin _).symm).trans
      (Equiv.sumCompl (IsInteriorIndex Z P T hconj))

@[simp] theorem orderedInteriorEndpointEquiv_inl
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (j : Fin (Fintype.card (InteriorIndex Z P T hconj))) :
    orderedInteriorEndpointEquiv Z P T hconj (Sum.inl j) =
      (orderedInteriorEquiv Z P T hconj j).1 := by
  simp [orderedInteriorEndpointEquiv]

/-- The same interior compression, now with a specified ordinate ordering. -/
def orderedCanonicalInteriorCompression
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    CentralSimpleSelection
      (canonicalCentralSelection Z P T hconj hreal hPois hc).selection.V
      (Fintype.card (InteriorIndex Z P T hconj))
      (Fintype.card (EndpointIndex Z P T hconj)) :=
  CentralSimpleSelection.ofEquiv _ (orderedInteriorEndpointEquiv Z P T hconj)
    (canonicalCentralSelection Z P T hconj hreal hPois hc).selection.retained_col_le

/-- Interior retained zero data at one height.  Positivity is an explicit
premise; no artificial atom is inserted at empty heights. -/
def interiorRetainedZeroData
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hr : 0 < Fintype.card (InteriorIndex Z P T hconj)) :
    RetainedZeroData Z T (Fintype.card (InteriorIndex Z P T hconj)) where
  r_pos := hr
  rho j :=
    (orderedRetainedEquiv Z P T hconj
      (orderedInteriorEquiv Z P T hconj j).1).1.1
  dyadic j :=
    (orderedRetainedEquiv Z P T hconj
      (orderedInteriorEquiv Z P T hconj j).1).2
  onLine j := (retainedAtomToCentralZero Z P T hconj
    (orderedRetainedEquiv Z P T hconj
      (orderedInteriorEquiv Z P T hconj j).1)).2.1.2
  simple j := (retainedAtomToCentralZero Z P T hconj
    (orderedRetainedEquiv Z P T hconj
      (orderedInteriorEquiv Z P T hconj j).1)).2.2
  ordinate_strictMono := by
    intro i j hij
    exact orderedRetainedEquiv_ordinate_strictMono Z P T hconj
      ((orderedInteriorEquiv Z P T hconj).strictMono hij)

/-- The ordered compression matrix is literally the matrix attached to the
ordered interior retained-zero data. -/
theorem orderedCanonicalInteriorCompression_V_eq_retainedV
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (hr : 0 < Fintype.card (InteriorIndex Z P T hconj)) :
    (orderedCanonicalInteriorCompression Z P T hconj hreal hPois hc).V =
      (interiorRetainedZeroData Z P T hconj hr).V P := by
  have hcard : Fintype.card (InteriorIndex Z P T hconj) ≤
      Fintype.card (RetainedAtom Z P T hconj) := by
    simpa using (Fintype.card_subtype_le (IsInteriorIndex Z P T hconj))
  have hrAll : 0 < Fintype.card (RetainedAtom Z P T hconj) :=
    hr.trans_le hcard
  rw [show
    (orderedCanonicalInteriorCompression Z P T hconj hreal hPois hc).V =
      fun i j =>
        (canonicalCentralSelection Z P T hconj hreal hPois hc).selection.V i
          ((orderedInteriorEquiv Z P T hconj j).1) by rfl]
  rw [canonicalCentralSelection_V_eq_retainedV
    Z P T hconj hreal hPois hc hrAll]
  rfl

/-- Eventual positivity is kept as a genuine analytic premise, rather than
being hidden by a non-semantic filler at exceptional heights. -/
def EventuallyInteriorPositive
    (Z : ZeroConfig) (P : Params) : Prop :=
  ∀ᶠ T in atTop, 0 < Fintype.card
    (InteriorIndex Z (P.atV CurrentWindow.window T) T ZeroSide.phiHatConj)

theorem eventually_nonempty_interiorRetainedZeroData
    {Z : ZeroConfig} {P : Params}
    (hpos : EventuallyInteriorPositive Z P) :
    ∀ᶠ T in atTop, Nonempty
      (RetainedZeroData Z T (Fintype.card
        (InteriorIndex Z (P.atV CurrentWindow.window T) T
          ZeroSide.phiHatConj))) := by
  filter_upwards [hpos] with T hT
  exact ⟨interiorRetainedZeroData Z (P.atV CurrentWindow.window T) T
    ZeroSide.phiHatConj hT⟩

end Zeta23Ext.CurrentInteriorRetentionBridge
