/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentCentralAssembler
import Zeta23Ext.CurrentInfiniteKernel

/-!
# Interior-margin retained atoms

The Poisson complement is not uniformly small for atoms arbitrarily close to
`T` or `2T`.  This module makes the required compression explicit.  Its
physical endpoint margin is `sqrt L / L`, so its lattice-scaled margin is
`sqrt L -> infinity`, while it is eventually shorter than a unit interval.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Filter Matrix Finset Set Asymptotics
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentInteriorRetention

open Zeta23
open Zeta23.ZeroSide
open Zeta23Ext.CurrentCentralSimple
open Zeta23Ext.CurrentCentralSelection
open Zeta23Ext.CurrentCentralAssembler
open Zeta23Ext.CurrentCompactGram
open Zeta23Ext.CurrentInfiniteKernel

/-- Margin in lattice units. -/
def marginScale (P : Params) (T : ℝ) : ℝ := Real.sqrt (P.L T)

/-- The corresponding physical ordinate margin. -/
def physicalMargin (P : Params) (T : ℝ) : ℝ := marginScale P T / P.L T

theorem tendsto_marginScale {P : Params} (hP : P.Valid) :
    Tendsto (marginScale P) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp (Params.tendsto_L_of_valid hP)

theorem eventually_physicalMargin_pos {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 0 < physicalMargin P T := by
  filter_upwards [(Params.tendsto_L_of_valid hP).eventually_gt_atTop 0] with T hL
  unfold physicalMargin marginScale
  positivity

theorem eventually_physicalMargin_le_one {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, physicalMargin P T ≤ 1 := by
  filter_upwards [(Params.tendsto_L_of_valid hP).eventually_ge_atTop 1] with T hL
  unfold physicalMargin marginScale
  rw [div_le_one (by linarith)]
  exact Real.sqrt_le_self_iff.mpr (Or.inr hL)

/-- Interior membership for the increasing enumeration of canonical central
simple atoms.  Both inequalities point inward. -/
def IsInteriorIndex (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (j : Fin (Fintype.card (RetainedAtom Z P T hconj))) : Prop :=
  let gamma := ((((orderedRetainedEquiv Z P T hconj j).1.1 :
    ZeroSide.ZI Z T) : ℂ).im)
  physicalMargin P T ≤ gamma - T ∧
    physicalMargin P T ≤ 2 * T - gamma

abbrev InteriorIndex (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :=
  {j : Fin (Fintype.card (RetainedAtom Z P T hconj)) //
    IsInteriorIndex Z P T hconj j}

abbrev EndpointIndex (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :=
  {j : Fin (Fintype.card (RetainedAtom Z P T hconj)) //
    ¬ IsInteriorIndex Z P T hconj j}

noncomputable instance interiorIndexFintype
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fintype (InteriorIndex Z P T hconj) := Fintype.ofFinite _

noncomputable instance endpointIndexFintype
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fintype (EndpointIndex Z P T hconj) := Fintype.ofFinite _

/-- Canonical interior/endpoint partition of the already-central columns. -/
def interiorEndpointEquiv
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) :
    Fin (Fintype.card (InteriorIndex Z P T hconj)) ⊕
        Fin (Fintype.card (EndpointIndex Z P T hconj)) ≃
      Fin (Fintype.card (RetainedAtom Z P T hconj)) := by
  classical
  exact (Equiv.sumCongr (Fintype.equivFin _).symm
    (Fintype.equivFin _).symm).trans (Equiv.sumCompl (IsInteriorIndex Z P T hconj))

/-- Matrix compression compatible with `LossyMomentData.compressInterior`. -/
def canonicalInteriorCompression
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    CentralSimpleSelection
      (canonicalCentralSelection Z P T hconj hreal hPois hc).selection.V
      (Fintype.card (InteriorIndex Z P T hconj))
      (Fintype.card (EndpointIndex Z P T hconj)) :=
  CentralSimpleSelection.ofEquiv _ (interiorEndpointEquiv Z P T hconj)
    (canonicalCentralSelection Z P T hconj hreal hPois hc).selection.retained_col_le

/-- The retained interior atom is at least `sqrt L` lattice units from the
left endpoint. -/
theorem interior_scaled_left
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    {hconj : ZeroSide.PhiHatConj T P}
    (hL : 0 < P.L T) (j : InteriorIndex Z P T hconj) :
    marginScale P T ≤ P.L T *
      (((((orderedRetainedEquiv Z P T hconj j.1).1.1 :
        ZeroSide.ZI Z T) : ℂ).im) - T) := by
  have h := j.2.1
  unfold physicalMargin at h
  rw [div_le_iff₀ hL] at h
  simpa [mul_comm] using h

/-- The retained interior atom is at least `sqrt L` lattice units from the
right endpoint. -/
theorem interior_scaled_right
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    {hconj : ZeroSide.PhiHatConj T P}
    (hL : 0 < P.L T) (j : InteriorIndex Z P T hconj) :
    marginScale P T ≤ P.L T *
      (2 * T - ((((orderedRetainedEquiv Z P T hconj j.1).1.1 :
        ZeroSide.ZI Z T) : ℂ).im)) := by
  have h := j.2.2
  unfold physicalMargin at h
  rw [div_le_iff₀ hL] at h
  simpa [mul_comm] using h

/-! ## Endpoint deletion count -/

/-- Two unit windows containing all atoms removed by the shrinking physical
margin, once that margin is at most one. -/
def endpointZeroSet (Z : ZeroConfig) (T : ℝ) : Set ℂ :=
  Z.window T (T + 1) ∪ Z.window (2 * T - 1) (2 * T)

lemma endpointZeroSet_finite (Z : ZeroConfig) (T : ℝ) :
    (endpointZeroSet Z T).Finite :=
  (Z.window_finite T (T + 1)).union (Z.window_finite (2 * T - 1) (2 * T))

noncomputable instance endpointZeroSetFintype (Z : ZeroConfig) (T : ℝ) :
    Fintype ↥(endpointZeroSet Z T) := (endpointZeroSet_finite Z T).fintype

/-- A deleted endpoint index maps to its underlying zero in one of the two
unit endpoint windows. -/
def endpointIndexToZero
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hpos : 0 < physicalMargin P T) (hle : physicalMargin P T ≤ 1) :
    EndpointIndex Z P T hconj → ↥(endpointZeroSet Z T) := fun j => by
  let a := orderedRetainedEquiv Z P T hconj j.1
  let gamma : ℝ := ((a.1.1 : ZeroSide.ZI Z T) : ℂ).im
  have hcentral : T < gamma ∧ gamma ≤ 2 * T := a.2
  have hcarrier : ((a.1.1 : ZeroSide.ZI Z T) : ℂ) ∈ Z.carrier :=
    (retainedAtomToCentralZero Z P T hconj a).2.1.1.1
  have hnot : ¬(physicalMargin P T ≤ gamma - T ∧
      physicalMargin P T ≤ 2 * T - gamma) := by
    simpa only [IsInteriorIndex, gamma, a] using j.2
  rw [not_and_or] at hnot
  refine ⟨((a.1.1 : ZeroSide.ZI Z T) : ℂ), ?_⟩
  unfold endpointZeroSet
  rcases hnot with hleft | hright
  · left
    exact ⟨hcarrier, hcentral.1, by linarith [lt_of_not_ge hleft]⟩
  · right
    exact ⟨hcarrier, by linarith [lt_of_not_ge hright], hcentral.2⟩

theorem endpointIndexToZero_injective
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hpos : 0 < physicalMargin P T) (hle : physicalMargin P T ≤ 1) :
    Function.Injective (endpointIndexToZero Z P T hconj hpos hle) := by
  intro i j hij
  apply Subtype.ext
  apply (orderedRetainedEquiv Z P T hconj).injective
  apply retainedAtom_ordinate_injective Z P T hconj
  have hc := congrArg (fun z : ↥(endpointZeroSet Z T) => (z.1 : ℂ).im) hij
  exact hc

/-- The number of additionally deleted columns is bounded in the correct
direction by the two multiplicity-weighted unit zero counts. -/
theorem card_endpointIndex_le_counts
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hpos : 0 < physicalMargin P T) (hle : physicalMargin P T ≤ 1) :
    Fintype.card (EndpointIndex Z P T hconj) ≤
      Z.N T (T + 1) + Z.N (2 * T - 1) (2 * T) := by
  calc
    Fintype.card (EndpointIndex Z P T hconj)
        ≤ Fintype.card ↥(endpointZeroSet Z T) :=
          Fintype.card_le_of_injective _
            (endpointIndexToZero_injective Z P T hconj hpos hle)
    _ = (endpointZeroSet Z T).ncard := Set.fintypeCard_eq_ncard _
    _ ≤ (Z.window T (T + 1)).ncard +
        (Z.window (2 * T - 1) (2 * T)).ncard := Set.ncard_union_le _ _
    _ ≤ Z.N T (T + 1) + Z.N (2 * T - 1) (2 * T) :=
      Nat.add_le_add
        (Z.ncard_le_finsum_mult T (T + 1) subset_rfl)
        (Z.ncard_le_finsum_mult (2 * T - 1) (2 * T) subset_rfl)

/-- The interior deletion count is `o(N(T,2T))`.  Only the local-count part
of Riemann--von Mangoldt is needed for the upper bound; its main term supplies
the comparison `log T = o(N(T,2T))`. -/
theorem endpointDeletion_isLittleO_N
    {Z : ZeroConfig} {P : Params} (hP : P.Valid)
    (hR : RiemannVonMangoldt Z)
    (hconj : ∀ T, ZeroSide.PhiHatConj T P) :
    (fun T => (Fintype.card (EndpointIndex Z P T (hconj T)) : ℝ))
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A0, hA0, hloc⟩ := hR.local_count
  have hO : (fun T =>
      (Fintype.card (EndpointIndex Z P T (hconj T)) : ℝ))
      =O[atTop] Real.log := by
    refine IsBigO.of_bound (4 * A0) ?_
    filter_upwards [eventually_physicalMargin_pos hP,
      eventually_physicalMargin_le_one hP, eventually_ge_atTop (4 : ℝ)] with
        T hm0 hm1 hT
    have hcard := card_endpointIndex_le_counts Z P T (hconj T) hm0 hm1
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
    push_cast at hcard
    have hcardR :
        (Fintype.card (EndpointIndex Z P T (hconj T)) : ℝ) ≤
          (Z.N T (T + 1) : ℝ) + (Z.N (2 * T - 1) (2 * T) : ℝ) := by
      exact_mod_cast hcard
    have hright' : (Z.N (2 * T - 1) (2 * T) : ℝ) ≤
        A0 * Real.log (|2 * T - 1| + 3) := by
      convert hright using 1 <;> ring
    have hA00 : 0 ≤ A0 := by linarith
    calc
      (Fintype.card (EndpointIndex Z P T (hconj T)) : ℝ)
          ≤ (Z.N T (T + 1) : ℝ) + (Z.N (2 * T - 1) (2 * T) : ℝ) := hcardR
      _ ≤ A0 * Real.log (|T| + 3) +
          A0 * Real.log (|2 * T - 1| + 3) := add_le_add hleft hright'
      _ ≤ A0 * (2 * Real.log T) + A0 * (2 * Real.log T) := by gcongr
      _ = 4 * A0 * Real.log T := by ring
  exact hO.trans_isLittleO
    (Assembly.isLittleO_N_of_isLittleO_Tl Z hR Assembly.isLittleO_log_Tl)

/-! ## Pointwise endpoint-tail bound -/

lemma Wfun_le_of_lower
    {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F)
    {Delta x : ℝ} (hDelta : 0 < Delta) (hDx : Delta ≤ x) :
    PrimeSide.Wfun c p x ≤
      (2 / Delta) ^ 2 + p.h⁻¹ * (4 / Delta) := by
  have hx : 0 < x := hDelta.trans_le hDx
  calc
    PrimeSide.Wfun c p x ≤ (2 / x) ^ 2 + p.h⁻¹ * (4 / x) :=
      Wfun_le_four hF hx
    _ ≤ (2 / Delta) ^ 2 + p.h⁻¹ * (4 / Delta) := by
      have hi : 1 / x ≤ 1 / Delta := one_div_le_one_div_of_le hDelta hDx
      have hh : 0 ≤ p.h⁻¹ := inv_nonneg.mpr (PrimeSide.Setting.h_pos hF.L_pos).le
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      gcongr

/-- Explicit normalized Poisson-complement error at lattice margin `q`.
The final term reflects that the rightmost grid point may lie up to one mesh
`2*pi/L` beyond the physical endpoint. -/
def rhoMarginError (q : ℝ) : ℝ :=
  16 / q ^ 2 + 8 / (Real.pi * q) + 8 / (q - 2 * Real.pi) ^ 2

/-- A point whose physical distance from each endpoint is at least `q/L`
has normalized omitted-grid mass bounded solely in terms of `q`. -/
theorem normalized_rho_le_rhoMarginError
    {P : Params} {T gamma c : ℝ}
    (hT : 0 < T) (hL : 0 < P.L T)
    (ha : 1 / 2 ≤ P.a T)
    (hlocal : PrimeSide.LocalHypsCoreW c
      (P.toSetting T) (P.localFun T))
    {q : ℝ} (hq : 2 * Real.pi < q)
    (hleft : q / P.L T ≤ gamma - T)
    (hright : q / P.L T ≤ 2 * T - gamma) :
    PrimeSide.rho (P.toSetting T) (P.localFun T) gamma /
      (P.a T * P.L T ^ 2) ≤ rhoMarginError q := by
  let p := P.toSetting T
  let F := P.localFun T
  let Delta := q / P.L T
  have hDelta : 0 < Delta := div_pos (lt_trans (by positivity) hq) hL
  have hgamma : gamma ∈ Icc p.T (2 * p.T) := by
    simp only [p, Params.toSetting_T]
    constructor <;> linarith
  have hrho := PrimeSide.rho_le_majorant hlocal hT hgamma
  have hWL := Wfun_le_of_lower hlocal hDelta hleft
  have hWR := Wfun_le_of_lower hlocal hDelta hright
  have hmesh : p.h = 2 * Real.pi / P.L T := by
    simp [p, PrimeSide.Setting.h]
  have hgridGap : Delta - p.h < p.tau p.d - gamma := by
    have htd := PrimeSide.tau_d_gt (p := p) hL hT
    have hpT : p.T = T := by rfl
    rw [hpT] at htd
    linarith
  have hgap0 : 0 < Delta - p.h := by
    rw [hmesh]
    exact sub_pos.mpr (div_lt_div_of_pos_right hq hL)
  have hgap : 0 < p.tau p.d - gamma := hgap0.trans hgridGap
  have hpsi0 := PrimeSide.psiA_nonneg_of hlocal (p.tau p.d - gamma)
  have hpsi := PrimeSide.psiA_le_div_abs (cϱ := c) (p := p) hgap.ne'
  rw [abs_of_pos hgap] at hpsi
  have hinvGap : 1 / (p.tau p.d - gamma) ≤ 1 / (Delta - p.h) :=
    one_div_le_one_div_of_le hgap0 hgridGap.le
  have hpsiSq : PrimeSide.psiA c p (p.tau p.d - gamma) ^ 2 ≤
      (2 / (Delta - p.h)) ^ 2 := by
    calc
      PrimeSide.psiA c p (p.tau p.d - gamma) ^ 2
          ≤ (2 / (p.tau p.d - gamma)) ^ 2 :=
        pow_le_pow_left₀ hpsi0 hpsi 2
      _ ≤ (2 / (Delta - p.h)) ^ 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        gcongr
  have hrho' : PrimeSide.rho p F gamma ≤
      2 * ((2 / Delta) ^ 2 + p.h⁻¹ * (4 / Delta)) +
        (2 / (Delta - p.h)) ^ 2 := by
    calc
      PrimeSide.rho p F gamma ≤
          PrimeSide.Wfun c p (gamma - p.T) +
            PrimeSide.Wfun c p (2 * p.T - gamma) +
              PrimeSide.psiA c p (p.tau p.d - gamma) ^ 2 := hrho
      _ ≤ ((2 / Delta) ^ 2 + p.h⁻¹ * (4 / Delta)) +
            ((2 / Delta) ^ 2 + p.h⁻¹ * (4 / Delta)) +
              (2 / (Delta - p.h)) ^ 2 := by
        exact add_le_add (add_le_add (by simpa [p] using hWL)
          (by simpa [p] using hWR)) hpsiSq
      _ = 2 * ((2 / Delta) ^ 2 + p.h⁻¹ * (4 / Delta)) +
            (2 / (Delta - p.h)) ^ 2 := by ring
  have ha0 : 0 < P.a T := by linarith
  have hden : 0 < P.a T * P.L T ^ 2 := by positivity
  have hnorm :
      PrimeSide.rho p F gamma /
          (P.a T * P.L T ^ 2) ≤
        (2 * ((2 / Delta) ^ 2 + p.h⁻¹ * (4 / Delta)) +
          (2 / (Delta - p.h)) ^ 2) /
          ((1 / 2) * P.L T ^ 2) := by
    apply (div_le_div_of_nonneg_right hrho' hden.le).trans
    have hh0 : 0 ≤ p.h⁻¹ := inv_nonneg.mpr (PrimeSide.Setting.h_pos hlocal.L_pos).le
    have hnum0 : 0 ≤ 2 * ((2 / Delta) ^ 2 + p.h⁻¹ * (4 / Delta)) +
        (2 / (Delta - p.h)) ^ 2 := by
      exact add_nonneg (mul_nonneg (by norm_num)
        (add_nonneg (sq_nonneg _) (mul_nonneg hh0 (by positivity)))) (sq_nonneg _)
    exact div_le_div_of_nonneg_left hnum0 (by positivity)
      (mul_le_mul_of_nonneg_right ha (sq_nonneg _))
  change PrimeSide.rho p F gamma /
      (P.a T * P.L T ^ 2) ≤ _
  calc
    PrimeSide.rho p F gamma /
        (P.a T * P.L T ^ 2)
        ≤ (2 * ((2 / Delta) ^ 2 + p.h⁻¹ * (4 / Delta)) +
          (2 / (Delta - p.h)) ^ 2) /
          ((1 / 2) * P.L T ^ 2) := hnorm
    _ = rhoMarginError q := by
      unfold rhoMarginError Delta
      rw [hmesh]
      field_simp [hL.ne', (sub_pos.mpr hq).ne']
      ring

theorem tendsto_rhoMarginError_marginScale {P : Params} (hP : P.Valid) :
    Tendsto (fun T => rhoMarginError (marginScale P T)) atTop (nhds 0) := by
  have hq := tendsto_marginScale hP
  have hq2 : Tendsto (fun T => marginScale P T ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hq
  have hpiq : Tendsto (fun T => Real.pi * marginScale P T) atTop atTop :=
    hq.const_mul_atTop Real.pi_pos
  have hsub : Tendsto (fun T => marginScale P T - 2 * Real.pi) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-(2 * Real.pi)) hq)
  have hsub2 : Tendsto (fun T => (marginScale P T - 2 * Real.pi) ^ 2)
      atTop atTop := (tendsto_pow_atTop two_ne_zero).comp hsub
  have h1 : Tendsto (fun T => 16 / marginScale P T ^ 2) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hq2
  have h2 : Tendsto (fun T => 8 / (Real.pi * marginScale P T))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hpiq
  have h3 : Tendsto (fun T => 8 / (marginScale P T - 2 * Real.pi) ^ 2)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hsub2
  simpa [rhoMarginError] using (h1.add h2).add h3

/-- One-height tail estimate for every atom selected by the canonical
interior compression. -/
theorem interiorIndex_normalized_rho_le
    {Z : ZeroConfig} {P : Params} {T c : ℝ}
    (hT : 0 < T) (hL : 0 < P.L T)
    (ha : 1 / 2 ≤ P.a T)
    (hlocal : PrimeSide.LocalHypsCoreW c
      (P.toSetting T) (P.localFun T))
    (hq : 2 * Real.pi < marginScale P T)
    {hconj : ZeroSide.PhiHatConj T P}
    (j : InteriorIndex Z P T hconj) :
    PrimeSide.rho (P.toSetting T) (P.localFun T)
        ((((orderedRetainedEquiv Z P T hconj j.1).1.1 :
          ZeroSide.ZI Z T) : ℂ).im) /
      (P.a T * P.L T ^ 2) ≤
      rhoMarginError (marginScale P T) := by
  apply normalized_rho_le_rhoMarginError hT hL ha hlocal hq
  · exact j.2.1
  · exact j.2.2

/-- The canonical current-window interior indices satisfy the exact uniform
rho-tail estimate eventually.  This is the analytic producer needed before
reindexing these columns as a `RetainedZeroData` family. -/
theorem eventually_current_interior_rho_tail
    {Z : ZeroConfig} {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    ∀ᶠ T in atTop,
      ∀ j : InteriorIndex Z (P.atV CurrentWindow.window T) T
          ZeroSide.phiHatConj,
        PrimeSide.rho ((P.atV CurrentWindow.window T).toSetting T)
            ((P.atV CurrentWindow.window T).localFun T)
            ((((orderedRetainedEquiv Z (P.atV CurrentWindow.window T) T
                ZeroSide.phiHatConj j.1).1.1 : ZeroSide.ZI Z T) : ℂ).im) /
          ((P.atV CurrentWindow.window T).a T *
            (P.atV CurrentWindow.window T).L T ^ 2) ≤
          rhoMarginError (marginScale P T) := by
  have hlocal := CurrentCompactGram.eventually_currentLocalHypsCore hP hcert
  filter_upwards [hlocal, Params.eventually_w8 hP,
    (Params.tendsto_L_of_valid hP).eventually_gt_atTop 0,
    (tendsto_marginScale hP).eventually_gt_atTop (2 * Real.pi),
    eventually_gt_atTop (0 : ℝ)] with T hlocalT h8 hL hq hT
  intro j
  have hW := CurrentWindowAdmissibility.admWindow_current hP hcert h8
  have ha := CurrentAnalyticBridge.current_a_half hP hcert h8 hW
  have htail := interiorIndex_normalized_rho_le hT
    (P := P.atV CurrentWindow.window T) hL ha hlocalT
    (by simpa [marginScale] using hq) j
  simpa [marginScale] using htail

end Zeta23Ext.CurrentInteriorRetention
