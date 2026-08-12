/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowAdmissibility
import Zeta23Ext.CurrentSpan
import Zeta23Ext.CurrentZetaAssembly
import Zeta23.XiPrime.Inputs
import Zeta23.XiPrime.Coeff.Reexpansion

/-!
# Instantiating the current-window analytic interface

This module connects the proved admissibility of the current cosine window to
the generic upstream zero- and prime-side APIs.  It also constructs the
retained atom matrix from the *actual* upstream evaluation vectors.  The
paper-specific deletion theorem (the positive-index/count seam) and the
compact-uniform current-kernel limit remain explicit; they are not available
in the pinned upstream development.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Filter Matrix Finset MeasureTheory Set Topology
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentAnalyticInstantiation

open Zeta23
open Zeta23.XiPrime
open Zeta23Ext
open Zeta23Ext.CurrentAnalyticBridge

/-! ## Admissibility and the generic analytic packages -/

/-- The current certificate discharges the complete generic zero-side bundle. -/
theorem currentWindowZeroSide_of_certificate {Z : ZeroConfig} {P : Params}
    (hP : P.Valid) (hR : RiemannVonMangoldt Z)
    (hcert : CurrentWindow.WindowCertificate) :
    XiPrime.WindowZeroSide Z P (P.atV CurrentWindow.window) :=
  currentWindowZeroSide hP hR hcert
    (CurrentWindowAdmissibility.currentWindowAdmissibility hP hcert)

/-- Unconditional actual-zeta specialization of the generic zero side. -/
theorem zeta_currentWindowZeroSide {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    XiPrime.WindowZeroSide zetaZeroConfig P (P.atV CurrentWindow.window) :=
  currentWindowZeroSide_of_certificate hP riemannVonMangoldt_zeta hcert

/-- The certified lower bound for `H(v)` is exactly the upper bound on the
moment constant needed by the stability bridge. -/
lemma current_c1_inv_le (hcert : CurrentWindow.WindowCertificate) :
    (CurrentWindow.c1 CurrentWindow.window)⁻¹ ≤ 2 - Current.Hcert := by
  have h := hcert.H_lower
  rw [CurrentWindow.Hcert_eq_current] at h
  unfold CurrentWindow.H at h
  rw [one_div] at h
  linarith

/-- Fourth-power comparison needed by the prime-side `AdmFamily` package. -/
lemma current_phiV_fourth_ge {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (u : ℝ) :
    9 / 16 * P.phi T u ^ 4 ≤ P.phiV CurrentWindow.window T u ^ 4 := by
  have hsq := current_phiV_sq_ge hP hcert h8 u
  have h0 : 0 ≤ P.phi T u ^ 2 := sq_nonneg _
  have h1 : 0 ≤ P.phiV CurrentWindow.window T u ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg
    (P.phiV CurrentWindow.window T u ^ 2 - 3 / 4 * P.phi T u ^ 2)]

/-- For `18w ≤ L`, the current modulated window has normalized fourth
moment at least `1/2`.  This supplies the extra field of the upstream
prime-side `AdmFamily`, rather than retaining it as a new assumption. -/
theorem current_bv_half {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) {T : ℝ}
    (h18 : 18 * P.w ≤ P.L T) :
    1 / 2 ≤ AdmWindow.bv (P.phiV CurrentWindow.window T) (P.L T) := by
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have h8 : 8 * P.w ≤ P.L T := by linarith
  have h2 : 2 * P.w ≤ P.L T := by linarith
  have hW := CurrentWindowAdmissibility.admWindow_current hP hcert h8
  have hintV : Integrable (fun u => P.phiV CurrentWindow.window T u ^ 4) :=
    hW.integrable_pow (by norm_num)
  have hintP : Integrable (fun u => 9 / 16 * P.phi T u ^ 4) :=
    ((Params.phi_continuous hP (by linarith)).fun_pow 4 |>.integrable_of_hasCompactSupport
      ((Params.phi_hasCompactSupport hP).comp_left
        (g := fun t => t ^ 4) (by norm_num))).const_mul _
  have hcmp : 9 / 16 * ∫ u, P.phi T u ^ 4 ≤
      ∫ u, P.phiV CurrentWindow.window T u ^ 4 := by
    rw [← integral_const_mul]
    exact integral_mono hintP hintV (current_phiV_fourth_ge hP hcert h8)
  have hb : 1 - 2 * P.w / P.L T ≤ P.b T :=
    Taper.one_sub_le_bConst hP.taper hw0 h2
  have hbdef : P.b T = (P.L T)⁻¹ * ∫ u, P.phi T u ^ 4 := rfl
  have hratio : 2 * P.w / P.L T ≤ 1 / 9 := by
    rw [div_le_iff₀ hL]
    linarith
  unfold AdmWindow.bv
  rw [hbdef] at hb
  have hLi : 0 < (P.L T)⁻¹ := inv_pos.mpr hL
  calc
    (1 : ℝ) / 2 ≤ 9 / 16 * (1 - 2 * P.w / P.L T) := by linarith
    _ ≤ 9 / 16 * ((P.L T)⁻¹ * ∫ u, P.phi T u ^ 4) := by gcongr
    _ = (P.L T)⁻¹ * (9 / 16 * ∫ u, P.phi T u ^ 4) := by ring
    _ ≤ (P.L T)⁻¹ * ∫ u, P.phiV CurrentWindow.window T u ^ 4 :=
      mul_le_mul_of_nonneg_left hcmp hLi.le

/-- The current modulated windows form an upstream admissible family. -/
theorem current_admFamily {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    XiPrime.AdmFamily P (fun T => P.phiV CurrentWindow.window T)
      (XiPrime.cMod P.ϱ CurrentWindowAdmissibility.factorA
        CurrentWindowAdmissibility.factorB) := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    ((Params.tendsto_L_of_valid hP).eventually_ge_atTop (18 * P.w))
  refine ⟨T₀, fun T hT => ?_⟩
  have h18 := hT₀ T hT
  exact ⟨CurrentWindowAdmissibility.admWindow_current hP hcert
      (by linarith [hP.one_le_w]),
    current_bv_half hP hcert h18⟩

/-- Same admissible family, in the exact `P.atV` spelling consumed upstream. -/
theorem current_admFamily_atV {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    XiPrime.AdmFamily P (fun T => (P.atV CurrentWindow.window T).phi T)
      (XiPrime.cMod P.ϱ CurrentWindowAdmissibility.factorA
        CurrentWindowAdmissibility.factorB) := by
  have heq : (fun T => (P.atV CurrentWindow.window T).phi T) =
      fun T => P.phiV CurrentWindow.window T :=
    funext fun T => Params.atV_phi_valid T hP CurrentWindow.window_even
  rw [heq]
  exact current_admFamily hP hcert

/-- All prime-side moment bookkeeping for the current window follows from
the generic theorem.  The sole window-specific primitive left here is the
displayed `cRatio` limit; this limit is not among the pinned upstream
quartic/flat results. -/
theorem current_coeffMoments {Z : ZeroConfig} {P : Params}
    {F : XiPrime.CoeffFamily} (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate) (hF : F.Hyps)
    (hR : RiemannVonMangoldt Z) {cinf : ℝ} (hcinf : 0 < cinf)
    (hratio : Tendsto (fun T => ThmD.cRatio (P.lam1 T)
      (AdmWindow.av ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (AdmWindow.bv ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (XiPrime.JD F.D
        (AdmWindow.gv ((P.atV CurrentWindow.window T).phi T))
        (P.L T) (Zeta23.l T))) atTop (𝓝 cinf)) :
    XiPrime.CoeffMoments Z (P.atV CurrentWindow.window) F cinf⁻¹ := by
  exact XiPrime.coeffMoments_atV hP hlam (current_admFamily_atV hP hcert)
    hF gammaFacts MV.mv_hilbert XiPrime.ppInput_of_PP hR hcinf hratio

/-- The generic two-trace transfer also applies to the current admissible
family.  Its true remaining primitives are the explicit formula and the
coefficient re-expansion. -/
theorem current_traceTransfer {Z : ZeroConfig} {P : Params}
    {F : XiPrime.CoeffFamily} (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate) (hR : RiemannVonMangoldt Z)
    (hEF : XiPrime.XiEF Z (P.atV CurrentWindow.window))
    {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hE : XiPrime.Reexpansion F e ρ₀ A T₀) :
    XiPrime.XiTraceTransfer Z (P.atV CurrentWindow.window) F := by
  obtain ⟨C, hC, hMV⟩ := MV.mv_hilbert
  have hW := currentWindowZeroSide_of_certificate hP hR hcert
  exact XiPrime.xiTraceTransfer_of Z _ F P hP hlam
    (fun _ => ⟨rfl, rfl⟩)
    (XiPrime.localHypsCore_eventually hP
      (current_admFamily_atV hP hcert)) gammaFacts
    ⟨1 / 2, by norm_num, hW.a_half⟩ hR hEF hρ₀ hE
    (XiPrime.frobSq_Ppart_le XiPrime.ppInput_of_PP hMV hC _ _
      ⟨hP.lam_pos, hP.lam_le_one⟩)

/-- Current-window `GzMoments` from the two exact analytic primitives above.
No current theorem is replaced by a flat/quartic-window theorem. -/
theorem current_gzMoments {Z : ZeroConfig} {P : Params}
    {F : XiPrime.CoeffFamily} (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate) (hF : F.Hyps)
    (hR : RiemannVonMangoldt Z) {cinf : ℝ} (hcinf : 0 < cinf)
    (hratio : Tendsto (fun T => ThmD.cRatio (P.lam1 T)
      (AdmWindow.av ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (AdmWindow.bv ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (XiPrime.JD F.D
        (AdmWindow.gv ((P.atV CurrentWindow.window T).phi T))
        (P.L T) (Zeta23.l T))) atTop (𝓝 cinf))
    (hEF : XiPrime.XiEF Z (P.atV CurrentWindow.window))
    {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hE : XiPrime.Reexpansion F e ρ₀ A T₀) :
    XiPrime.GzMoments Z (P.atV CurrentWindow.window) cinf⁻¹ :=
  XiPrime.gzMoments_of_transfer Z _ F (inv_nonneg.mpr hcinf.le)
    (current_coeffMoments hP hlam hcert hF hR hcinf hratio)
    (current_traceTransfer hP hlam hcert hR hEF hρ₀ hE)

/-- Natural specialization in which the prime-side ratio converges to the
paper's exact `c₁(window)`.  In this spelling the certificate itself supplies
the later inequality `kappa ≤ 2 - Hcert`. -/
theorem current_gzMoments_c1 {Z : ZeroConfig} {P : Params}
    {F : XiPrime.CoeffFamily} (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate) (hF : F.Hyps)
    (hR : RiemannVonMangoldt Z)
    (hc1 : 0 < CurrentWindow.c1 CurrentWindow.window)
    (hratio : Tendsto (fun T => ThmD.cRatio (P.lam1 T)
      (AdmWindow.av ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (AdmWindow.bv ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (XiPrime.JD F.D
        (AdmWindow.gv ((P.atV CurrentWindow.window T).phi T))
        (P.L T) (Zeta23.l T))) atTop
          (𝓝 (CurrentWindow.c1 CurrentWindow.window)))
    (hEF : XiPrime.XiEF Z (P.atV CurrentWindow.window))
    {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hE : XiPrime.Reexpansion F e ρ₀ A T₀) :
    XiPrime.GzMoments Z (P.atV CurrentWindow.window)
      (CurrentWindow.c1 CurrentWindow.window)⁻¹ :=
  current_gzMoments hP hlam hcert hF hR hc1 hratio hEF hρ₀ hE

/-! ## Actual retained zeros and their upstream atom matrix -/

/-- An ordered retained family inside the actual upstream enlarged zero
window.  The fields say precisely that the retained elements are simple,
on-line zeros in the narrower dyadic interval. -/
structure RetainedZeroData (Z : ZeroConfig) (T : ℝ) (r : ℕ) where
  r_pos : 0 < r
  rho : Fin r → ZeroSide.ZI Z T
  dyadic : ∀ j, T < ((rho j : ZeroSide.ZI Z T) : ℂ).im ∧
    ((rho j : ZeroSide.ZI Z T) : ℂ).im ≤ 2 * T
  onLine : ∀ j, ((rho j : ZeroSide.ZI Z T) : ℂ).re = 1 / 2
  simple : ∀ j, Z.mult ((rho j : ZeroSide.ZI Z T) : ℂ) = 1
  ordinate_strictMono : StrictMono (fun j => ((rho j : ZeroSide.ZI Z T) : ℂ).im)

namespace RetainedZeroData

variable {Z : ZeroConfig} {P : Params} {T : ℝ} {r : ℕ}

/-- The paper's normalized retained ordinates. -/
def y (h : RetainedZeroData Z T r) (j : Fin r) : ℝ :=
  CurrentSpan.normalizedOrdinate T ((h.rho j : ZeroSide.ZI Z T) : ℂ).im

lemma y_strictMono (h : RetainedZeroData Z T r) (hl : 0 < Zeta23.l T) :
    StrictMono h.y := by
  intro i j hij
  have him := h.ordinate_strictMono hij
  unfold y CurrentSpan.normalizedOrdinate
  have hc : 0 < Zeta23.l T / (2 * Real.pi) := by positivity
  calc
    Zeta23.l T * (((h.rho i : ZeroSide.ZI Z T) : ℂ).im - T) /
          (2 * Real.pi) =
        (Zeta23.l T / (2 * Real.pi)) *
          (((h.rho i : ZeroSide.ZI Z T) : ℂ).im - T) := by ring
    _ < (Zeta23.l T / (2 * Real.pi)) *
          (((h.rho j : ZeroSide.ZI Z T) : ℂ).im - T) :=
      mul_lt_mul_of_pos_left (sub_lt_sub_right him T) hc
    _ = Zeta23.l T * (((h.rho j : ZeroSide.ZI Z T) : ℂ).im - T) /
          (2 * Real.pi) := by ring

lemma rho_injective (h : RetainedZeroData Z T r) : Function.Injective h.rho := by
  intro i j hij
  apply h.ordinate_strictMono.injective
  exact congrArg (fun z : ZeroSide.ZI Z T => (z : ℂ).im) hij

/-- The retained complex zero set, forgetting its ordering. -/
def retainedSet (h : RetainedZeroData Z T r) : Set ℂ :=
  Set.range fun j => ((h.rho j : ZeroSide.ZI Z T) : ℂ)

lemma retainedSet_ncard (h : RetainedZeroData Z T r) : h.retainedSet.ncard = r := by
  rw [retainedSet, Set.ncard_range_of_injective]
  · simp
  · exact Subtype.val_injective.comp h.rho_injective

/-- For the actual zeta configuration, an ordered retained family is
automatically bounded by `N0simple`; no cardinality assumption remains. -/
theorem ncard_le_N0simple
    (h : RetainedZeroData zetaZeroConfig T r) :
    r ≤ Zeta23.N0simple T (2 * T) := by
  rw [← h.retainedSet_ncard]
  apply CurrentZetaAssembly.retained_ncard_le_N0simple
  intro rho hrho
  obtain ⟨j, rfl⟩ := hrho
  have hcarrier := ZeroSide.mem_carrier_of_mem_ZI
    zetaZeroConfig T (h.rho j).2
  change IsNontrivialZero ((h.rho j : ZeroSide.ZI zetaZeroConfig T) : ℂ) at hcarrier
  exact ⟨⟨⟨hcarrier, h.dyadic j⟩, h.onLine j⟩, h.simple j⟩

/-- The exact normalized upstream evaluation-vector matrix for the retained
zeros.  Its columns are the paper's retained atoms. -/
def V (h : RetainedZeroData Z T r) (P : Params) :
    Matrix (Fin (P.d T)) (Fin r) ℂ :=
  fun k j => ZeroSide.evalVec Z T P (h.rho j) k /
    (Real.sqrt (P.a T * P.L T ^ 2) : ℂ)

/-- Poisson summation gives the required unit column bound for the actual
retained atom matrix. -/
theorem colSq_V_le (h : RetainedZeroData Z T r)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P)
    (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) (j : Fin r) :
    StabilityRankTrace.colSq (h.V P) j ≤ 1 := by
  have hz : h.rho j ∈ (ZeroSide.blockData Z T P hconj).onLine := by
    rw [ZeroSide.ZeroBlockData.mem_onLine]
    exact (ZeroSide.mkData_σ_eq_iff Z T _ _ (h.rho j)).2 (h.onLine j)
  have hsum := ZeroSide.sum_normSq_v_le Z T P hconj hreal hPois (h.rho j) hz
  unfold StabilityRankTrace.colSq V
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    ∑ x, (‖ZeroSide.evalVec Z T P (h.rho j) x‖ /
          Real.sqrt (P.a T * P.L T ^ 2)) ^ 2 =
        (∑ x, ‖ZeroSide.evalVec Z T P (h.rho j) x‖ ^ 2) /
          (P.a T * P.L T ^ 2) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      rw [div_pow, Real.sq_sqrt hc.le]
    _ ≤ 1 := (div_le_one hc).2 (by simpa [ZeroSide.blockData] using hsum)

/-- The exact remainder after extracting the retained atoms from the
normalized full zero-side matrix. -/
def Q (h : RetainedZeroData Z T r) (P : Params) :
    Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  P.hat T (Z.Gz P T) - h.V P * (h.V P)ᴴ

lemma V_mul_add_Q (h : RetainedZeroData Z T r) (P : Params) :
    h.V P * (h.V P)ᴴ + h.Q P = P.hat T (Z.Gz P T) := by
  simp [Q]

/-- Hermitianity of the concrete remainder follows from Hermitianity of the
actual normalized full zero-side matrix. -/
theorem Q_isHermitian (h : RetainedZeroData Z T r) (P : Params)
    (hfull : (P.hat T (Z.Gz P T)).IsHermitian) : (h.Q P).IsHermitian := by
  have hpsd : (h.V P * (h.V P)ᴴ).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (h.V P)ᴴ
  exact hfull.sub hpsd.isHermitian

/-- The paper-specific deletion/inertia assertion, stated for the concrete
remainder just defined.  Construction of `V`, construction of `Q`, column
bounds, and the matrix identity are not fields of this primitive. -/
structure DeletionSeam (h : RetainedZeroData Z T r) (P : Params)
    (b : ℕ) (N : ℝ) : Prop where
  full_hermitian : (P.hat T (Z.Gz P T)).IsHermitian
  positive_index : RHLinalg.posIndex (h.Q_isHermitian P full_hermitian) ≤ b
  count_seam : 3 * (r : ℝ) + 4 * (b : ℝ) ≤ (r : ℝ) + 2 * N

/-- The exact retained construction supplies the bridge's decomposition
record once the narrow deletion/inertia seam is known. -/
theorem toRetainedDecomposition (h : RetainedZeroData Z T r)
    {b : ℕ} {N : ℝ} (hdel : DeletionSeam h P b N)
    (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P)
    (hPois : ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    CurrentAnalyticBridge.RetainedDecomposition b N (h.V P) (h.Q P) where
  col_le := h.colSq_V_le hconj hreal hPois hc
  Q_hermitian := h.Q_isHermitian P hdel.full_hermitian
  positive_index := hdel.positive_index
  count_seam := hdel.count_seam

/-- Endpoint membership and the exact normalization discharge the assembly's
span inequality for every retained family. -/
theorem spanControl (h : RetainedZeroData Z T r) (hl : 0 ≤ Zeta23.l T) :
    h.y ⟨r - 1, Nat.sub_lt h.r_pos Nat.zero_lt_one⟩ - h.y ⟨0, h.r_pos⟩ ≤
      (Z.N T (2 * T) : ℝ) + CurrentSpan.spanError Z T := by
  apply CurrentSpan.spanControl_of_normalized_endpoint_bounds Z h.r_pos h.y
      rfl rfl hl
  · exact (h.dyadic ⟨0, h.r_pos⟩).1.le
  · exact (h.dyadic ⟨r - 1, Nat.sub_lt h.r_pos Nat.zero_lt_one⟩).2

/-- The one genuinely current-kernel Gram primitive, now stated for the
actual retained upstream atom matrix and exact normalized ordinates. -/
def CurrentKernelCloseness (h : RetainedZeroData Z T r) (P : Params)
    (err : ℝ) : Prop :=
  ∀ i j : Fin r, (i : ℕ) < (j : ℕ) →
    h.y j - h.y i < CurrentBlock.D →
    ‖((h.V P)ᴴ * h.V P) i j -
      (CurrentWindow.normalizedKernel (h.y j - h.y i) : ℂ)‖ ≤ err

/-- Exact conversion of the narrow compact-kernel primitive to the bridge's
ordinary entrywise Gram record. -/
theorem entrywiseGramData (h : RetainedZeroData Z T r) (P : Params)
    (hcert : CurrentWindow.WindowCertificate) {err : ℝ} (herr : 0 ≤ err)
    (hclose : CurrentKernelCloseness h P err) :
    CurrentAnalyticBridge.EntrywiseGramData h.y (h.V P) err :=
  ⟨hcert, herr, hclose⟩

end RetainedZeroData

/-! ## Eventual moment data for the concrete retained matrices -/

/-- `GzMoments` plus the narrow deletion seam yields the bridge's moment data
for the concrete upstream retained atoms.  Poisson summation, conjugation,
real-valuedness on the real axis, column bounds, and the matrix identity are
all discharged here. -/
theorem eventually_retainedMomentData
    {Z : ZeroConfig} {P : Params} (hP : P.Valid)
    (hR : RiemannVonMangoldt Z)
    (hcert : CurrentWindow.WindowCertificate) {kappa : ℝ}
    (hM : XiPrime.GzMoments Z (P.atV CurrentWindow.window) kappa)
    (hkappa : kappa ≤ 2 - Current.Hcert)
    {r b : ℝ → ℕ}
    (ret : ∀ T, RetainedZeroData Z T (r T))
    (hdel : ∀ᶠ T in atTop,
      RetainedZeroData.DeletionSeam (ret T)
        (P.atV CurrentWindow.window T) (b T) (Z.N T (2 * T) : ℝ))
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ T in atTop,
      CurrentAnalyticBridge.MomentData (b T) (Z.N T (2 * T) : ℝ)
        (delta * (Z.N T (2 * T) : ℝ))
        (delta * (Z.N T (2 * T) : ℝ))
        ((ret T).V (P.atV CurrentWindow.window T))
        ((ret T).Q (P.atV CurrentWindow.window T)) := by
  let Pf := P.atV CurrentWindow.window
  have hW : XiPrime.WindowZeroSide Z P Pf :=
    currentWindowZeroSide_of_certificate hP hR hcert
  have hL : ∀ᶠ T in atTop, 0 < (Pf T).L T := by
    have hbase := (Params.tendsto_L_of_valid hP).eventually_gt_atTop 0
    filter_upwards [hbase] with T hT
    simpa [Pf, Params.L] using hT
  have hret : ∀ᶠ T in atTop,
      CurrentAnalyticBridge.RetainedDecomposition (b T)
        (Z.N T (2 * T) : ℝ) ((ret T).V (Pf T)) ((ret T).Q (Pf T)) := by
    filter_upwards [hdel, hW.poisson, hW.a_half, hL] with T hdelT hPois ha hLT
    apply (ret T).toRetainedDecomposition hdelT
      ZeroSide.phiHatConj ZeroSide.phiHatReal hPois
    have ha0 : 0 < (Pf T).a T := by linarith
    positivity
  have hmatrix : ∀ᶠ T in atTop,
      (ret T).V (Pf T) * ((ret T).V (Pf T))ᴴ + (ret T).Q (Pf T) =
        (Pf T).hat T (Z.Gz (Pf T) T) :=
    Eventually.of_forall fun T => (ret T).V_mul_add_Q (Pf T)
  exact CurrentAnalyticBridge.eventually_momentData_of_gzMoments hM hkappa
    (fun T => (ret T).V (Pf T)) (fun T => (ret T).Q (Pf T))
    hret hmatrix hdelta

/-! ## The exact compact-uniform primitive -/

/-- Compact-uniform Gram convergence for the actual retained upstream atoms.
The error function may depend on the compact radius, as in the standard
definition of locally uniform convergence.  This is the narrow current-kernel
statement not present in the pinned upstream tree. -/
def CompactUniformCurrentGram {Z : ZeroConfig} (P : Params)
    {r : ℝ → ℕ} (ret : ∀ T, RetainedZeroData Z T (r T)) : Prop :=
  ∀ D : ℝ, 0 < D → ∃ err : ℝ → ℝ,
    Tendsto err atTop (𝓝 0) ∧
    ∀ᶠ T in atTop, 0 ≤ err T ∧
      ∀ i j : Fin (r T),
        |(ret T).y j - (ret T).y i| ≤ D →
        ‖(((ret T).V (P.atV CurrentWindow.window T))ᴴ *
            (ret T).V (P.atV CurrentWindow.window T)) i j -
          (CurrentWindow.normalizedKernel
            ((ret T).y j - (ret T).y i) : ℂ)‖ ≤ err T

/-- Extract the precise fixed-`D` entrywise records consumed by the block
assembly from compact-uniform convergence. -/
theorem eventually_entrywiseGramData_of_compactUniform
    {Z : ZeroConfig} {P : Params} {r : ℝ → ℕ}
    (ret : ∀ T, RetainedZeroData Z T (r T))
    (hcert : CurrentWindow.WindowCertificate)
    (hgram : CompactUniformCurrentGram P ret) :
    ∃ err : ℝ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ T in atTop,
        CurrentAnalyticBridge.EntrywiseGramData (ret T).y
          ((ret T).V (P.atV CurrentWindow.window T)) (err T) := by
  obtain ⟨err, herr, hclose⟩ := hgram CurrentBlock.D CurrentBlock.D_pos
  refine ⟨err, herr, ?_⟩
  filter_upwards [hclose, Zeta23.Assembly.eventually_l_pos] with T hT hl
  apply (ret T).entrywiseGramData (P.atV CurrentWindow.window T) hcert hT.1
  intro i j hij hdist
  apply hT.2 i j
  rw [abs_of_nonneg]
  · exact hdist.le
  · exact ((ret T).y_strictMono hl).monotone (Nat.le_of_lt hij) |> sub_nonneg.mpr

end Zeta23Ext.CurrentAnalyticInstantiation
