/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentInteriorAnalyticPackage

/-!
# Asymptotic deletion bookkeeping for the interior compression

This file proves that both deletion charges in the concrete interior package
are negligible on the assembler's enlarged-count scale.  No retained family
and no positivity of the simple-zero count is used.
-/

noncomputable section
set_option maxHeartbeats 4000000

open Filter Asymptotics
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentInteriorAsymptotic

open Zeta23
open Zeta23.ZeroSide
open Zeta23Ext.CurrentCentralSelection
open Zeta23Ext.CurrentInteriorRetention
open Zeta23Ext.CurrentInteriorRetentionBridge
open Zeta23Ext.CurrentInteriorAnalyticPackage
open Zeta23Ext.CurrentCentralAssembler
open Zeta23Ext.CurrentRetainedWithLoss
open Zeta23Ext.CurrentCentralSimple
open Zeta23Ext.CurrentAnalyticBridge
open Zeta23Ext.CurrentAnalyticInstantiation

/-- The enlarged-window boundary count appearing in the canonical central
selection, written without proof-dependent selection data. -/
def centralBoundaryDeletion (Z : ZeroConfig) (T : ℝ) : ℕ :=
  Z.s1 T - Z.N0s T (2 * T)

theorem centralBoundaryDeletion_le_NII
    (Z : ZeroConfig) {T : ℝ} (hT : 0 ≤ T) :
    centralBoundaryDeletion Z T ≤ Assembly.NII Z T := by
  unfold centralBoundaryDeletion
  have hs1 := Assembly.s1_le Z hT
  omega

/-- Riemann--von Mangoldt's local count estimate makes the enlarged boundary
count little-o of the dyadic count. -/
theorem NII_isLittleO_N
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    (fun T => (Assembly.NII Z T : ℝ)) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A0, hA0, hloc⟩ := hR.local_count
  obtain ⟨C, hC⟩ := Tail.eventually_NII_le Z hA0 hloc
  have hO : (fun T => (Assembly.NII Z T : ℝ)) =O[atTop]
      (fun T => Real.sqrt T * Zeta23.l T) := by
    refine IsBigO.of_bound |C| ?_
    filter_upwards [hC, Assembly.eventually_l_pos,
      eventually_ge_atTop (0 : ℝ)] with T hbound hl hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hl.le)]
    calc
      (Assembly.NII Z T : ℝ) ≤ C * (Real.sqrt T * Zeta23.l T) := by
        simpa [mul_assoc] using hbound
      _ ≤ |C| * (Real.sqrt T * Zeta23.l T) := by
        gcongr
        exact le_abs_self C
  exact hO.trans_isLittleO
    (Assembly.isLittleO_N_of_isLittleO_Tl Z hR
      Assembly.isLittleO_sqrt_mul_l_Tl)

theorem NII_isLittleO_NIprime
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    (fun T => (Assembly.NII Z T : ℝ)) =o[atTop]
      (fun T => (Z.NIprime T : ℝ)) :=
  (NII_isLittleO_N Z hR).trans_isBigO (N_isBigO_NIprime Z)

/-- The canonical central deletion is negligible on the enlarged-count
scale. -/
theorem centralBoundaryDeletion_isLittleO_NIprime
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    (fun T => (centralBoundaryDeletion Z T : ℝ)) =o[atTop]
      (fun T => (Z.NIprime T : ℝ)) := by
  have hO : (fun T => (centralBoundaryDeletion Z T : ℝ)) =O[atTop]
      (fun T => (Assembly.NII Z T : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg _), one_mul]
    exact_mod_cast centralBoundaryDeletion_le_NII Z hT
  exact hO.trans_isLittleO (NII_isLittleO_NIprime Z hR)

/-- Proof-independent spelling of the full deletion loss used by the actual
current-window interior compression. -/
def currentInteriorDeletionLoss
    (Z : ZeroConfig) (P : Params) (T : ℝ) : ℝ :=
  2 * (centralBoundaryDeletion Z T : ℝ) +
    2 * (Fintype.card
      (EndpointIndex Z (P.atV CurrentWindow.window T) T
        ZeroSide.phiHatConj) : ℝ)

theorem currentInteriorDeletionLoss_nonneg
    (Z : ZeroConfig) (P : Params) (T : ℝ) :
    0 ≤ currentInteriorDeletionLoss Z P T := by
  unfold currentInteriorDeletionLoss
  positivity

/-- The complete central-plus-interior deletion loss is `o(NIprime)`. -/
theorem currentInteriorDeletionLoss_isLittleO_NIprime
    {Z : ZeroConfig} {P : Params} (hP : P.Valid)
    (hR : RiemannVonMangoldt Z) :
    currentInteriorDeletionLoss Z P =o[atTop]
      (fun T => (Z.NIprime T : ℝ)) := by
  exact (centralBoundaryDeletion_isLittleO_NIprime Z hR).const_mul_left 2 |>.add
    ((currentEndpointDeletion_isLittleO_NIprime hP hR).const_mul_left 2)

/-- At one height, the proof-independent loss is definitionally the loss
charged by `InteriorHeightPremises.toLossyFinite`. -/
theorem interiorCountLoss_eq_current
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    interiorCountLoss Z P T hconj hreal hPois hc =
      2 * (centralBoundaryDeletion Z T : ℝ) +
        2 * (Fintype.card (EndpointIndex Z P T hconj) : ℝ) := by
  simp [interiorCountLoss, centralBoundaryDeletion,
    canonicalCentralSelection_deleted]

/-! ## Scaled span error -/

lemma scaledWindowLength_eq_lam_mul_normalizationScale
    (P : Params) (T : ℝ) :
    scaledWindowLength P T =
      P.lam * CurrentSpan.normalizationScale T := by
  simp [scaledWindowLength, CurrentSpan.normalizationScale, Params.L]
  ring

/-- For the theorem's strict `lambda < 1` regime, the actual lattice-scaled
dyadic length is eventually already below the dyadic zero count.  Hence the
one-sided span error against the larger `NIprime` count vanishes exactly;
using an absolute scaled-span error here would incorrectly leave a
`(1-lambda)N` term. -/
theorem eventually_centralScaledSpanError_eq_zero
    {Z : ZeroConfig} {P : Params} (hP : P.Valid) (hlam : P.lam < 1)
    (hR : RiemannVonMangoldt Z) :
    ∀ᶠ T in atTop, centralScaledSpanError Z P T = 0 := by
  let c : ℝ := (1 - P.lam) / (2 * P.lam)
  have hc : 0 < c := div_pos (sub_pos.mpr hlam)
    (mul_pos (by norm_num) hP.lam_pos)
  have herr := isLittleO_iff.mp
    (CurrentSpan.signedSpanError_isLittleO_count Z hR) hc
  filter_upwards [herr, CurrentSpan.eventually_count_pos Z hR,
    eventually_ge_atTop (0 : ℝ)] with T he hN hT
  have he' : CurrentSpan.signedSpanError Z T ≤
      c * (Z.N T (2 * T) : ℝ) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hN] at he
    exact (le_abs_self _).trans he
  have hcId : P.lam * c = (1 - P.lam) / 2 := by
    dsimp [c]
    field_simp [hP.lam_pos.ne']
  have hscale : scaledWindowLength P T ≤ (Z.N T (2 * T) : ℝ) := by
    rw [scaledWindowLength_eq_lam_mul_normalizationScale]
    unfold CurrentSpan.signedSpanError at he'
    have hlam0 := hP.lam_pos
    have hlam1 := hP.lam_le_one
    rw [show CurrentSpan.normalizationScale T =
        (Z.N T (2 * T) : ℝ) +
          (CurrentSpan.normalizationScale T - (Z.N T (2 * T) : ℝ)) by ring]
    nlinarith [mul_le_mul_of_nonneg_left he' hP.lam_pos.le]
  have hNle : (Z.N T (2 * T) : ℝ) ≤ (Z.NIprime T : ℝ) := by
    exact_mod_cast (show Z.N T (2 * T) ≤ Z.NIprime T by
      rw [Assembly.NIprime_eq Z hT]
      exact Nat.le_add_right _ _)
  unfold centralScaledSpanError
  rw [max_eq_left]
  linarith

theorem centralScaledSpanError_isLittleO_NIprime
    {Z : ZeroConfig} {P : Params} (hP : P.Valid) (hlam : P.lam < 1)
    (hR : RiemannVonMangoldt Z) :
    centralScaledSpanError Z P =o[atTop]
      (fun T => (Z.NIprime T : ℝ)) := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [eventually_centralScaledSpanError_eq_zero hP hlam hR] with
      T hzero
  rw [hzero, norm_zero]
  exact mul_nonneg hc.le (norm_nonneg _)

/-! ## Non-circular interior positivity -/

/-- Moment stability itself forces the interior compression to be nonempty
once its total stability error is strictly smaller than the positive main
term.  This proof does not assume a retained-zero datum or a Gram theorem. -/
theorem interiorCard_pos_of_lossyStabilityError_lt
    (Z : ZeroConfig) (P : Params) (T R₁ R₂ : ℝ)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (hm : CentralAzMomentPremise Z P T (Z.NIprime T : ℝ) R₁ R₂)
    (hsmall : lossyStabilityError R₁ R₂
        (interiorCountLoss Z P T hconj hreal hPois hc) <
      Current.Hcert * (Z.NIprime T : ℝ)) :
    0 < Fintype.card (InteriorIndex Z P T hconj) := by
  let SI := orderedCanonicalInteriorCompression Z P T hconj hreal hPois hc
  have hmom0 := canonical_lossyMomentData Z P T R₁ R₂ hconj hreal hPois hc hm
  have hmom := CurrentCentralAssembler.LossyMomentData.compressInterior hmom0 SI
  have hstab := hmom.stabilitySeam
  have hdefect : 0 ≤ CurrentAssembly.globalDefect
      (Matrix.conjTranspose SI.V * SI.V)
      (Matrix.posSemidef_conjTranspose_mul_self SI.V) := by
    unfold CurrentAssembly.globalDefect
    exact Finset.sum_nonneg fun j _ => StabilityRankTrace.Psi_nonneg _
  have hposR : 0 < (Fintype.card (InteriorIndex Z P T hconj) : ℝ) := by
    have herrEq :
        lossyStabilityError R₁ R₂
          (2 * ((canonicalCentralSelection Z P T hconj hreal hPois hc).deleted : ℝ) +
            2 * (Fintype.card (EndpointIndex Z P T hconj) : ℝ)) =
        lossyStabilityError R₁ R₂
          (interiorCountLoss Z P T hconj hreal hPois hc) := by
      rfl
    change Current.Hcert * (Z.NIprime T : ℝ) +
        CurrentAssembly.globalDefect (Matrix.conjTranspose SI.V * SI.V)
          (Matrix.posSemidef_conjTranspose_mul_self SI.V) -
        lossyStabilityError R₁ R₂
          (2 * ((canonicalCentralSelection Z P T hconj hreal hPois hc).deleted : ℝ) +
            2 * (Fintype.card (EndpointIndex Z P T hconj) : ℝ)) ≤
          (Fintype.card (InteriorIndex Z P T hconj) : ℝ) at hstab
    rw [herrEq] at hstab
    linarith
  exact_mod_cast hposR

/-- Family form of the stability error charged by the current interior
compression. -/
def currentInteriorStabilityError
    (Z : ZeroConfig) (P : Params) (R₁ R₂ : ℝ → ℝ) (T : ℝ) : ℝ :=
  lossyStabilityError (R₁ T) (R₂ T)
    (currentInteriorDeletionLoss Z P T)

theorem currentInteriorStabilityError_isLittleO_NIprime
    {Z : ZeroConfig} {P : Params} (hP : P.Valid)
    (hR : RiemannVonMangoldt Z) {R₁ R₂ : ℝ → ℝ}
    (hR₁ : R₁ =o[atTop] (fun T => (Z.NIprime T : ℝ)))
    (hR₂ : R₂ =o[atTop] (fun T => (Z.NIprime T : ℝ))) :
    currentInteriorStabilityError Z P R₁ R₂ =o[atTop]
      (fun T => (Z.NIprime T : ℝ)) := by
  have hsum := (hR₁.const_mul_left 4).add hR₂ |>.add
    (currentInteriorDeletionLoss_isLittleO_NIprime hP hR)
  change (fun T => 4 * R₁ T + R₂ T +
    currentInteriorDeletionLoss Z P T) =o[atTop]
      (fun T => (Z.NIprime T : ℝ))
  exact hsum

theorem tendsto_NIprime_atTop (Z : ZeroConfig)
    (hR : RiemannVonMangoldt Z) :
    Tendsto (fun T => (Z.NIprime T : ℝ)) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [(Assembly.tendsto_N_atTop Z hR).eventually_ge_atTop b,
    eventually_ge_atTop (0 : ℝ)] with T hb hT
  exact hb.trans (by
    exact_mod_cast (show Z.N T (2 * T) ≤ Z.NIprime T by
      rw [Assembly.NIprime_eq Z hT]
      exact Nat.le_add_right _ _))

/-- If current-window Az moment errors are little-o, moment stability proves
eventual interior positivity.  This removes the formerly circular positivity
premise before the one-height retained data and Gram record are constructed. -/
theorem eventually_currentInterior_card_pos_of_moments
    {Z : ZeroConfig} {P : Params} (hP : P.Valid)
    (hR : RiemannVonMangoldt Z)
    (hcert : CurrentWindow.WindowCertificate)
    {R₁ R₂ : ℝ → ℝ}
    (hR₁ : R₁ =o[atTop] (fun T => (Z.NIprime T : ℝ)))
    (hR₂ : R₂ =o[atTop] (fun T => (Z.NIprime T : ℝ)))
    (hMom : ∀ᶠ T in atTop,
      CentralAzMomentPremise Z (P.atV CurrentWindow.window T) T
        (Z.NIprime T : ℝ) (R₁ T) (R₂ T)) :
    ∀ᶠ T in atTop, 0 < Fintype.card
      (InteriorIndex Z (P.atV CurrentWindow.window T) T
        ZeroSide.phiHatConj) := by
  let Np : ℝ → ℝ := fun T => (Z.NIprime T : ℝ)
  have herrO := currentInteriorStabilityError_isLittleO_NIprime
    hP hR hR₁ hR₂
  have hH : 0 < Current.Hcert / 2 := by norm_num [Current.Hcert]
  have herrSmall := isLittleO_iff.mp herrO hH
  have hNp := (tendsto_NIprime_atTop Z hR).eventually_gt_atTop 0
  have hzero := currentWindowZeroSide_of_certificate hP hR hcert
  filter_upwards [herrSmall, hNp, hMom, hzero.poisson,
    hzero.a_half, (Params.tendsto_L_of_valid hP).eventually_gt_atTop 0] with
      T herr hN hm hPois ha hL
  have hc : 0 < (P.atV CurrentWindow.window T).a T *
      (P.atV CurrentWindow.window T).L T ^ 2 := by
    simp only [Params.atV_L]
    positivity
  apply interiorCard_pos_of_lossyStabilityError_lt Z
    (P.atV CurrentWindow.window T) T (R₁ T) (R₂ T)
    ZeroSide.phiHatConj ZeroSide.phiHatReal hPois hc hm
  have herr' : currentInteriorStabilityError Z P R₁ R₂ T <
      Current.Hcert * (Z.NIprime T : ℝ) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hN] at herr
    have habs := (le_abs_self _).trans herr
    nlinarith [hN, show (0 : ℝ) < Current.Hcert by norm_num [Current.Hcert]]
  rw [interiorCountLoss_eq_current]
  simpa [currentInteriorStabilityError, currentInteriorDeletionLoss,
    centralBoundaryDeletion] using herr'

end Zeta23Ext.CurrentInteriorAsymptotic
