/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentAssembly
import Zeta23.Final

/-!
# Normalized dyadic span and its Riemann--von Mangoldt error

This file discharges the normalized-span part of Input 1.  If ordinates lie in
`(T,2T]`, their normalization by `log(T/(2*pi))/(2*pi)` has total span at most
`T log(T/(2*pi))/(2*pi)`.  The unconditional Riemann--von Mangoldt theorem in
Zeta23 then shows that this scale is `N(T,2T) + o(N(T,2T))`.

No zero-selection, simplicity, Gram-matrix, or Arb-certificate statement is
asserted here.  Those remain the finite-height inputs of `CurrentAssembly`.
-/

noncomputable section

open Filter Asymptotics Topology

namespace Zeta23Ext.CurrentSpan

open Zeta23

/-- The paper's normalized coordinate for an ordinate in the dyadic window. -/
def normalizedOrdinate (T gamma : ℝ) : ℝ :=
  Zeta23.l T * (gamma - T) / (2 * Real.pi)

/-- The length of the whole normalized dyadic window `[T,2T]`. -/
def normalizationScale (T : ℝ) : ℝ :=
  T * Zeta23.l T / (2 * Real.pi)

/-- The signed difference between the normalized window length and the zero count. -/
def signedSpanError (Z : ZeroConfig) (T : ℝ) : ℝ :=
  normalizationScale T - (Z.N T (2 * T) : ℝ)

/-- A nonnegative span error suitable for `CurrentAssembly.FiniteHeightInputs`. -/
def spanError (Z : ZeroConfig) (T : ℝ) : ℝ :=
  |signedSpanError Z T|

/-- The remainder in the upstream Riemann--von Mangoldt normalization. -/
private def rvmRemainder (Z : ZeroConfig) (T : ℝ) : ℝ :=
  (Z.N T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T

/-- Two ordinates in `[T,2T]` have normalized separation at most the full
normalized window length. -/
theorem normalizedOrdinate_sub_le_scale {T gammaLo gammaHi : ℝ}
    (hl : 0 ≤ Zeta23.l T) (hLo : T ≤ gammaLo) (hHi : gammaHi ≤ 2 * T) :
    normalizedOrdinate T gammaHi - normalizedOrdinate T gammaLo ≤
      normalizationScale T := by
  have hgap : gammaHi - gammaLo ≤ T := by linarith
  have hcoeff : 0 ≤ Zeta23.l T / (2 * Real.pi) := by positivity
  calc
    normalizedOrdinate T gammaHi - normalizedOrdinate T gammaLo =
        (Zeta23.l T / (2 * Real.pi)) * (gammaHi - gammaLo) := by
          simp [normalizedOrdinate]
          ring
    _ ≤ (Zeta23.l T / (2 * Real.pi)) * T :=
      mul_le_mul_of_nonneg_left hgap hcoeff
    _ = normalizationScale T := by simp [normalizationScale]; ring

/-- `T = o(T log(T/(2*pi)))`. -/
private theorem isLittleO_id_Tl :
    (fun T : ℝ => T) =o[atTop] (fun T => T * Zeta23.l T) := by
  refine (isLittleO_iff).2 fun c hc => ?_
  filter_upwards
    [Zeta23.Assembly.tendsto_l_atTop.eventually_ge_atTop c⁻¹,
      Zeta23.Assembly.eventually_l_pos, eventually_gt_atTop (0 : ℝ)]
      with T hlower hl hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT,
    abs_of_pos (mul_pos hT hl)]
  have hone : 1 ≤ c * Zeta23.l T := by
    have hmul := mul_le_mul_of_nonneg_left hlower hc.le
    rwa [mul_inv_cancel₀ hc.ne'] at hmul
  nlinarith

/-- The `O(log T)` remainder in Riemann--von Mangoldt is `o(T l(T))`. -/
private theorem rvmRemainder_isLittleO_Tl (Z : ZeroConfig)
    (hR : RiemannVonMangoldt Z) :
    rvmRemainder Z =o[atTop] (fun T => T * Zeta23.l T) := by
  obtain ⟨C, T0, hmain⟩ := hR.main
  have hO : rvmRemainder Z =O[atTop] Real.log := by
    refine IsBigO.of_bound |C| ?_
    filter_upwards
      [eventually_ge_atTop T0, Zeta23.Assembly.eventually_log_nonneg]
      with T hT hlog
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog]
    exact (hmain T hT).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) hlog)
  exact hO.trans_isLittleO Zeta23.Assembly.isLittleO_log_Tl

/-- The signed normalized-span error is `o(T l(T))`. -/
theorem signedSpanError_isLittleO_Tl (Z : ZeroConfig)
    (hR : RiemannVonMangoldt Z) :
    signedSpanError Z =o[atTop] (fun T => T * Zeta23.l T) := by
  have hrem := (rvmRemainder_isLittleO_Tl Z hR).const_mul_left (-1 : ℝ)
  have hlinear := isLittleO_id_Tl.const_mul_left
    (-(Zeta23.Assembly.c₀ / (2 * Real.pi)))
  rw [show signedSpanError Z = fun T =>
      (-1 : ℝ) * rvmRemainder Z T +
        (-(Zeta23.Assembly.c₀ / (2 * Real.pi))) * T by
    funext T
    simp [signedSpanError, normalizationScale, rvmRemainder,
      Zeta23.Assembly.ell1_eq]
    ring]
  exact hrem.add hlinear

/-- Riemann--von Mangoldt upgrades the signed span error to `o(N(T,2T))`. -/
theorem signedSpanError_isLittleO_count (Z : ZeroConfig)
    (hR : RiemannVonMangoldt Z) :
    signedSpanError Z =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
  Zeta23.Assembly.isLittleO_N_of_isLittleO_Tl Z hR
    (signedSpanError_isLittleO_Tl Z hR)

/-- The nonnegative absolute span error is `o(N(T,2T))`. -/
theorem spanError_isLittleO_count (Z : ZeroConfig)
    (hR : RiemannVonMangoldt Z) :
    spanError Z =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  rw [show spanError Z = fun T => ‖signedSpanError Z T‖ by
    funext T
    simp [spanError, Real.norm_eq_abs]]
  exact (signedSpanError_isLittleO_count Z hR).norm_left

/-- The dyadic zero count is eventually strictly positive. -/
theorem eventually_count_pos (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    ∀ᶠ T in atTop, 0 < (Z.N T (2 * T) : ℝ) :=
  (Zeta23.Assembly.tendsto_N_atTop Z hR).eventually_gt_atTop 0

/-- Natural-number form of eventual positivity. -/
theorem eventually_count_nat_pos (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    ∀ᶠ T in atTop, 0 < Z.N T (2 * T) := by
  filter_upwards [eventually_count_pos Z hR] with T hT
  exact_mod_cast hT

/-- Pointwise comparison of the normalized window length with the zero count
and the explicit absolute error. -/
theorem normalizationScale_le_count_add_spanError (Z : ZeroConfig) (T : ℝ) :
    normalizationScale T ≤ (Z.N T (2 * T) : ℝ) + spanError Z T := by
  have habs := le_abs_self (signedSpanError Z T)
  simp only [signedSpanError, spanError] at habs ⊢
  linarith

/-- Direct discharge of the span-control inequality from endpoint membership
in the dyadic window and exact normalized coordinates. -/
theorem normalizedOrdinate_sub_le_count_add_spanError
    (Z : ZeroConfig) {T gammaLo gammaHi : ℝ}
    (hl : 0 ≤ Zeta23.l T) (hLo : T ≤ gammaLo) (hHi : gammaHi ≤ 2 * T) :
    normalizedOrdinate T gammaHi - normalizedOrdinate T gammaLo ≤
      (Z.N T (2 * T) : ℝ) + spanError Z T :=
  (normalizedOrdinate_sub_le_scale hl hLo hHi).trans
    (normalizationScale_le_count_add_spanError Z T)

/-- Exact shape of `CurrentAssembly.FiniteHeightInputs.spanControl`.  A caller
only has to identify the first and last retained coordinates with normalized
ordinates and prove that those ordinates belong to the dyadic window. -/
theorem spanControl_of_normalized_endpoint_bounds
    (Z : ZeroConfig) {r : ℕ} (hr : 0 < r) (y : Fin r → ℝ)
    {T gammaLo gammaHi : ℝ}
    (hfirst : y ⟨0, hr⟩ = normalizedOrdinate T gammaLo)
    (hlast : y ⟨r - 1, by omega⟩ = normalizedOrdinate T gammaHi)
    (hl : 0 ≤ Zeta23.l T) (hLo : T ≤ gammaLo) (hHi : gammaHi ≤ 2 * T) :
    y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩ ≤
      (Z.N T (2 * T) : ℝ) + spanError Z T := by
  rw [hfirst, hlast]
  exact normalizedOrdinate_sub_le_count_add_spanError Z hl hLo hHi

/-- Epsilon form of `spanError = o(N)`, ready for the filter-level capstone. -/
theorem eventually_spanError_le_mul_count (Z : ZeroConfig)
    (hR : RiemannVonMangoldt Z) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T in atTop, spanError Z T ≤ eps * (Z.N T (2 * T) : ℝ) := by
  have h := isLittleO_iff.mp (spanError_isLittleO_count Z hR) heps
  filter_upwards [h] with T hT
  simpa [Real.norm_eq_abs, spanError] using hT

/-- The pressure-weighted span contribution in `assembledBlockError` remains
`o(N)`. Thus this entire error component follows from the supplied
Riemann--von Mangoldt hypothesis; the zeta specialization below discharges
that hypothesis unconditionally. -/
theorem pressureSpanError_isLittleO_count (Z : ZeroConfig)
    (hR : RiemannVonMangoldt Z) :
    (fun T => Current.eta * Current.pressureCap * (249 / 250 : ℝ) * spanError Z T)
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  simpa only [mul_assoc] using
    (spanError_isLittleO_count Z hR).const_mul_left
      (Current.eta * Current.pressureCap * (249 / 250 : ℝ))

/-! ### Unconditional zeta specializations -/

/-- For the actual zeta zero count, the normalized-span error is `o(N(T,2T))`
with no hypotheses. -/
theorem zeta_spanError_isLittleO_count :
    spanError zetaZeroConfig =o[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) := by
  simpa using spanError_isLittleO_count zetaZeroConfig riemannVonMangoldt_zeta

/-- The actual dyadic zeta count is eventually positive. -/
theorem zeta_eventually_count_pos :
    ∀ᶠ T in atTop, 0 < Ncount T (2 * T) := by
  simpa using eventually_count_nat_pos zetaZeroConfig riemannVonMangoldt_zeta

/-- Unconditional epsilon packaging for the actual zeta span error. -/
theorem zeta_eventually_spanError_le_mul_count {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T in atTop,
      spanError zetaZeroConfig T ≤ eps * (Ncount T (2 * T) : ℝ) := by
  simpa using eventually_spanError_le_mul_count
    zetaZeroConfig riemannVonMangoldt_zeta heps

/-- Unconditional `o(N)` control of the exact pressure-weighted summand in
`CurrentAssembly.assembledBlockError`. -/
theorem zeta_pressureSpanError_isLittleO_count :
    (fun T => Current.eta * Current.pressureCap * (249 / 250 : ℝ) *
      spanError zetaZeroConfig T) =o[atTop]
        (fun T => (Ncount T (2 * T) : ℝ)) := by
  simpa using pressureSpanError_isLittleO_count
    zetaZeroConfig riemannVonMangoldt_zeta

/-- Actual-zeta endpoint span control, with an unconditional `o(N)` error. -/
theorem zeta_normalizedOrdinate_sub_le_count_add_spanError
    {T gammaLo gammaHi : ℝ}
    (hl : 0 ≤ Zeta23.l T) (hLo : T ≤ gammaLo) (hHi : gammaHi ≤ 2 * T) :
    normalizedOrdinate T gammaHi - normalizedOrdinate T gammaLo ≤
      (Ncount T (2 * T) : ℝ) + spanError zetaZeroConfig T := by
  simpa using normalizedOrdinate_sub_le_count_add_spanError
    zetaZeroConfig hl hLo hHi

/-- Zeta-specialized helper in the exact shape of the assembly's `spanControl`
field.  Its error is unconditionally `o(N)` by
`zeta_spanError_isLittleO_count`; no RvM hypothesis is exposed to the caller. -/
theorem zeta_spanControl_of_normalized_endpoint_bounds
    {r : ℕ} (hr : 0 < r) (y : Fin r → ℝ) {T gammaLo gammaHi : ℝ}
    (hfirst : y ⟨0, hr⟩ = normalizedOrdinate T gammaLo)
    (hlast : y ⟨r - 1, by omega⟩ = normalizedOrdinate T gammaHi)
    (hl : 0 ≤ Zeta23.l T) (hLo : T ≤ gammaLo) (hHi : gammaHi ≤ 2 * T) :
    y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩ ≤
      (Ncount T (2 * T) : ℝ) + spanError zetaZeroConfig T := by
  simpa using spanControl_of_normalized_endpoint_bounds
    zetaZeroConfig hr y hfirst hlast hl hLo hHi

end Zeta23Ext.CurrentSpan
