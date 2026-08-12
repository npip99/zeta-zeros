/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentAnalyticBridge
import Zeta23Ext.CurrentSpan

/-!
# Retained atoms with an explicit deletion loss

This module is an alternative to the exact-count `DeletionSeam` in
`CurrentAnalyticInstantiation`.  Compressing an original Gram decomposition
to a smaller retained set moves the discarded positive atoms into the
remainder.  Their rank must therefore be charged to the positive-index
allowance.  The resulting counting inequality has an explicit deletion loss;
it is generally false without that loss.

The module also fixes the ordinate normalization used by a parameter family:
the lattice spacing is controlled by `P.L T`, not by the endpoint value
`Zeta23.l T` unless `P.lam = 1`.
-/

noncomputable section

open Filter Matrix Finset Asymptotics
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentRetainedWithLoss

open Zeta23
open Zeta23Ext
open Zeta23Ext.CurrentAnalyticBridge

/-! ## Parameter-scaled ordinates -/

/-- The normalized ordinate matching the actual lattice spacing `2*pi/(P.L T)`. -/
def scaledOrdinate (P : Params) (T gamma : ℝ) : ℝ :=
  P.L T * (gamma - T) / (2 * Real.pi)

/-- The length of the whole dyadic interval in the actual parameter scale. -/
def scaledWindowLength (P : Params) (T : ℝ) : ℝ :=
  T * P.L T / (2 * Real.pi)

/-- A nonnegative span error against the zero count at the actual parameter scale. -/
def scaledSpanError (Z : ZeroConfig) (P : Params) (T : ℝ) : ℝ :=
  |scaledWindowLength P T - (Z.N T (2 * T) : ℝ)|

lemma scaledOrdinate_strictMono {P : Params} {T : ℝ} (hL : 0 < P.L T) :
    StrictMono (scaledOrdinate P T) := by
  intro x y hxy
  unfold scaledOrdinate
  have hc : 0 < P.L T / (2 * Real.pi) := by positivity
  calc
    P.L T * (x - T) / (2 * Real.pi) =
        (P.L T / (2 * Real.pi)) * (x - T) := by ring
    _ < (P.L T / (2 * Real.pi)) * (y - T) :=
      mul_lt_mul_of_pos_left (sub_lt_sub_right hxy T) hc
    _ = P.L T * (y - T) / (2 * Real.pi) := by ring

lemma scaledOrdinate_sub_le_windowLength {P : Params} {T gammaLo gammaHi : ℝ}
    (hL : 0 ≤ P.L T) (hLo : T ≤ gammaLo) (hHi : gammaHi ≤ 2 * T) :
    scaledOrdinate P T gammaHi - scaledOrdinate P T gammaLo ≤
      scaledWindowLength P T := by
  have hgap : gammaHi - gammaLo ≤ T := by linarith
  have hc : 0 ≤ P.L T / (2 * Real.pi) := by positivity
  calc
    scaledOrdinate P T gammaHi - scaledOrdinate P T gammaLo =
        (P.L T / (2 * Real.pi)) * (gammaHi - gammaLo) := by
          simp [scaledOrdinate]
          ring
    _ ≤ (P.L T / (2 * Real.pi)) * T := mul_le_mul_of_nonneg_left hgap hc
    _ = scaledWindowLength P T := by simp [scaledWindowLength]; ring

lemma scaledWindowLength_le_count_add_error (Z : ZeroConfig) (P : Params) (T : ℝ) :
    scaledWindowLength P T ≤
      (Z.N T (2 * T) : ℝ) + scaledSpanError Z P T := by
  unfold scaledSpanError
  linarith [le_abs_self (scaledWindowLength P T - (Z.N T (2 * T) : ℝ))]

/-! ## Principal compression and positive-index bookkeeping -/

/-- Data for compressing an original atom matrix into retained and discarded columns.

`V` contains the retained columns, `W` the discarded columns, and `Qoff` the
original remainder.  After compression the correct remainder is
`W Wᴴ + Qoff`; the discarded positive term cannot simply be dropped from the
matrix identity used by the stability theorem. -/
structure PrincipalCompression (d r deleted : ℕ) where
  V : Matrix (Fin d) (Fin r) ℂ
  W : Matrix (Fin d) (Fin deleted) ℂ
  Qoff : Matrix (Fin d) (Fin d) ℂ
  Qoff_hermitian : Qoff.IsHermitian

namespace PrincipalCompression

variable {d r deleted : ℕ} (h : PrincipalCompression d r deleted)

/-- The remainder after moving the discarded PSD columns out of the atom matrix. -/
def remainder : Matrix (Fin d) (Fin d) ℂ := h.W * h.Wᴴ + h.Qoff

lemma discarded_posSemidef : (h.W * h.Wᴴ).PosSemidef := by
  simpa using Matrix.posSemidef_conjTranspose_mul_self h.Wᴴ

lemma remainder_hermitian : h.remainder.IsHermitian :=
  h.discarded_posSemidef.isHermitian.add h.Qoff_hermitian

lemma discarded_rank_le : (h.W * h.Wᴴ).rank ≤ deleted := by
  have hw : h.W.rank ≤ deleted := by
    simpa using h.W.rank_le_card_width
  exact (rank_mul_le_left h.W h.Wᴴ).trans hw

/-- Discarding `deleted` columns costs at most `deleted` positive directions. -/
theorem remainder_posIndex_le {p : ℕ}
    (hoff : RHLinalg.posIndex h.Qoff_hermitian ≤ p) :
    RHLinalg.posIndex h.remainder_hermitian ≤ deleted + p := by
  calc
    RHLinalg.posIndex h.remainder_hermitian ≤
        RHLinalg.posIndex h.discarded_posSemidef.isHermitian +
          RHLinalg.posIndex h.Qoff_hermitian :=
      RHLinalg.posIndex_add_le h.discarded_posSemidef.isHermitian h.Qoff_hermitian
    _ = (h.W * h.Wᴴ).rank + RHLinalg.posIndex h.Qoff_hermitian := by
      rw [RHLinalg.posIndex_eq_rank_of_posSemidef h.discarded_posSemidef]
    _ ≤ deleted + p := Nat.add_le_add h.discarded_rank_le hoff

/-- Reassociate an original three-part decomposition after principal compression. -/
lemma retained_add_remainder :
    h.V * h.Vᴴ + h.remainder =
      h.V * h.Vᴴ + h.W * h.Wᴴ + h.Qoff := by
  simp only [remainder]
  abel

end PrincipalCompression

/-! ## The exact finite count loss -/

/-- If `deleted` simple on-line atoms are removed, the stability count seam
acquires the sharp elementary loss `2 * deleted`.

The original zero decomposition supplies `s1 + 2*s2 + 2*p ≤ N`.  The
retained atom count is `r = s1 - deleted`, while the new positive-index
allowance is `p + deleted`. -/
theorem count_seam_of_deleted
    {s1 s2 p r deleted N : ℕ}
    (hret : r + deleted = s1)
    (hcount : s1 + 2 * s2 + 2 * p ≤ N) :
    3 * (r : ℝ) + 4 * ((deleted + p : ℕ) : ℝ) ≤
      (r : ℝ) + 2 * (N : ℝ) + 2 * (deleted : ℝ) := by
  have hretR : (r : ℝ) + deleted = s1 := by exact_mod_cast hret
  have hcountR : (s1 : ℝ) + 2 * s2 + 2 * p ≤ N := by exact_mod_cast hcount
  push_cast
  nlinarith

/-! ## Loss-aware stability data -/

/-- A retained decomposition with an explicit real-valued count loss. -/
structure LossyRetainedDecomposition {d r : ℕ} (b : ℕ)
    (N countLoss : ℝ) (V : Matrix (Fin d) (Fin r) ℂ)
    (Q : Matrix (Fin d) (Fin d) ℂ) : Prop where
  col_le : ∀ j, StabilityRankTrace.colSq V j ≤ 1
  Q_hermitian : Q.IsHermitian
  positive_index : RHLinalg.posIndex Q_hermitian ≤ b
  countLoss_nonneg : 0 ≤ countLoss
  count_seam :
    3 * (r : ℝ) + 4 * (b : ℝ) ≤ (r : ℝ) + 2 * N + countLoss

/-- Canonical loss-aware retained decomposition obtained by discarding
`deleted` columns.  This is the concrete seam that the old exact-deletion
interface lacked: both the added positive-index allowance and the real count
loss are produced together. -/
theorem PrincipalCompression.toLossyRetainedDecomposition
    {d r deleted s1 s2 p N : ℕ} (h : PrincipalCompression d r deleted)
    (hcol : ∀ j, StabilityRankTrace.colSq h.V j ≤ 1)
    (hoff : RHLinalg.posIndex h.Qoff_hermitian ≤ p)
    (hret : r + deleted = s1)
    (hcount : s1 + 2 * s2 + 2 * p ≤ N) :
    LossyRetainedDecomposition (deleted + p) (N : ℝ)
      (2 * (deleted : ℝ)) h.V h.remainder where
  col_le := hcol
  Q_hermitian := h.remainder_hermitian
  positive_index := h.remainder_posIndex_le hoff
  countLoss_nonneg := by positivity
  count_seam := count_seam_of_deleted hret hcount

/-- Moment bounds paired with the correct lossy retained decomposition. -/
structure LossyMomentData {d r : ℕ} (b : ℕ)
    (N R₁ R₂ countLoss : ℝ) (V : Matrix (Fin d) (Fin r) ℂ)
    (Q : Matrix (Fin d) (Fin d) ℂ) : Prop
    extends LossyRetainedDecomposition b N countLoss V Q where
  trace_lower : N - R₁ ≤ RHLinalg.rtrace (V * Vᴴ + Q)
  frobenius_upper : RHLinalg.frobSq (V * Vᴴ + Q) ≤
    (2 - Current.Hcert) * N + R₂

/-- The exact stability error after deletion.  Each deleted-count loss unit
is charged once; this is sharper than absorbing the loss by inflating `N`. -/
def lossyStabilityError (R₁ R₂ countLoss : ℝ) : ℝ :=
  4 * R₁ + R₂ + countLoss

theorem LossyMomentData.stabilitySeam
    {d r b : ℕ} {N R₁ R₂ countLoss : ℝ}
    {V : Matrix (Fin d) (Fin r) ℂ} {Q : Matrix (Fin d) (Fin d) ℂ}
    (h : LossyMomentData b N R₁ R₂ countLoss V Q) :
    Current.Hcert * N +
        CurrentAssembly.globalDefect (Vᴴ * V)
          (Matrix.posSemidef_conjTranspose_mul_self V) -
        lossyStabilityError R₁ R₂ countLoss ≤ (r : ℝ) := by
  have hcount : 3 * (r : ℝ) + 4 * (b : ℝ) ≤
      ((r : ℝ) + countLoss) + 2 * N := by
    linarith [h.count_seam]
  have hs := Stability.stability_seam_moment h.col_le h.Q_hermitian
    h.positive_index hcount h.trace_lower h.frobenius_upper
  simp_rw [Bridge.Psi_eq] at hs
  unfold CurrentAssembly.globalDefect lossyStabilityError
  nlinarith

/-! ## Compatibility with the existing entrywise asymptotic capstone -/

/-- Inflate the bookkeeping count by half the deletion loss.  This converts
the lossy count seam into the legacy exact seam without asserting that the
inflated count is the actual zero count. -/
def effectiveCount (N countLoss : ℝ) : ℝ := N + countLoss / 2

/-- Matching trace error after the effective-count conversion. -/
def effectiveTraceError (R₁ countLoss : ℝ) : ℝ := R₁ + countLoss / 2

lemma two_sub_Hcert_nonneg : 0 ≤ 2 - Current.Hcert := by
  norm_num [Current.Hcert]

theorem LossyMomentData.toMomentData
    {d r b : ℕ} {N R₁ R₂ countLoss : ℝ}
    {V : Matrix (Fin d) (Fin r) ℂ} {Q : Matrix (Fin d) (Fin d) ℂ}
    (h : LossyMomentData b N R₁ R₂ countLoss V Q) :
    MomentData b (effectiveCount N countLoss)
      (effectiveTraceError R₁ countLoss) R₂ V Q where
  col_le := h.col_le
  Q_hermitian := h.Q_hermitian
  positive_index := h.positive_index
  count_seam := by
    unfold effectiveCount
    linarith [h.count_seam]
  trace_lower := by
    unfold effectiveCount effectiveTraceError
    simpa only [add_sub_add_right_eq_sub] using h.trace_lower
  frobenius_upper := by
    have hmul : (2 - Current.Hcert) * N ≤
        (2 - Current.Hcert) * effectiveCount N countLoss := by
      apply mul_le_mul_of_nonneg_left _ two_sub_Hcert_nonneg
      unfold effectiveCount
      linarith [h.countLoss_nonneg]
    nlinarith [h.frobenius_upper, hmul]

/-- One-height entrywise analytic data with the honest deletion loss exposed. -/
structure LossyFiniteEntrywiseAnalyticInputs
    (d r b : ℕ) (N spanError err R₁ R₂ countLoss : ℝ) where
  finiteWindow : CurrentWindow.FiniteWindowInputs
  r_pos : 0 < r
  N_nonneg : 0 ≤ N
  spanError_nonneg : 0 ≤ spanError
  y : Fin r → ℝ
  y_strictMono : StrictMono y
  V : Matrix (Fin d) (Fin r) ℂ
  Q : Matrix (Fin d) (Fin d) ℂ
  gram : EntrywiseGramData y V err
  moments : LossyMomentData b N R₁ R₂ countLoss V Q
  spanControl :
    y ⟨r - 1, by omega⟩ - y ⟨0, r_pos⟩ ≤ N + spanError
  delta_small :
    Current.eta * blockDelta (entryEnergyError err) ≤ Current.R

def LossyFiniteEntrywiseAnalyticInputs.toFiniteEntrywiseAnalyticInputs
    {d r b : ℕ} {N spanError err R₁ R₂ countLoss : ℝ}
    (h : LossyFiniteEntrywiseAnalyticInputs d r b N spanError err R₁ R₂ countLoss) :
    FiniteEntrywiseAnalyticInputs d r b
      (effectiveCount N countLoss) spanError err
      (effectiveTraceError R₁ countLoss) R₂ where
  finiteWindow := h.finiteWindow
  r_pos := h.r_pos
  N_nonneg := by
    unfold effectiveCount
    linarith [h.N_nonneg, h.moments.countLoss_nonneg]
  spanError_nonneg := h.spanError_nonneg
  y := h.y
  y_strictMono := h.y_strictMono
  V := h.V
  Q := h.Q
  gram := h.gram
  moments := h.moments.toMomentData
  spanControl := by
    unfold effectiveCount
    linarith [h.spanControl, h.moments.countLoss_nonneg]
  delta_small := h.delta_small

/-- Filter-level contract used to assemble independently developed retained,
moment, Gram, span, and finite-certificate lanes. -/
structure LossyAsymptoticEntrywiseInputs {X : Type*} (l : Filter X) where
  r : X → ℕ
  N : X → ℝ
  spanError : X → ℝ
  err : X → ℝ
  R₁ : X → ℝ
  R₂ : X → ℝ
  countLoss : X → ℝ
  countLoss_nonneg : ∀ x, 0 ≤ countLoss x
  eventuallyAnalytic : ∀ᶠ x in l, ∃ d b : ℕ,
    Nonempty (LossyFiniteEntrywiseAnalyticInputs d (r x) b
      (N x) (spanError x) (err x) (R₁ x) (R₂ x) (countLoss x))
  errorsAreSmall : ∀ eta > 0, ∀ᶠ x in l,
    stabilityError (effectiveTraceError (R₁ x) (countLoss x)) (R₂ x) +
        CurrentAssembly.assembledBlockError (r x)
          (blockDelta (entryEnergyError (err x))) (spanError x) ≤
      (1 - Current.R / (Current.m : ℝ)) * eta * N x

/-- The complete error charged by the compatibility route at one parameter.
In particular, `countLoss` occurs inside `effectiveTraceError`, so proving
this function is `o(N)` explicitly forces the deletion loss to be `o(N)` (or
to be absorbed by other, sharper component estimates). -/
def compatibilityTotalError {X : Type*}
    (r : X → ℕ) (spanError err R₁ R₂ countLoss : X → ℝ) (x : X) : ℝ :=
  stabilityError (effectiveTraceError (R₁ x) (countLoss x)) (R₂ x) +
    CurrentAssembly.assembledBlockError (r x)
      (blockDelta (entryEnergyError (err x))) (spanError x)

/-- The analytic error before the deletion charge is inserted. -/
def baseTotalError {X : Type*}
    (r : X → ℕ) (spanError err R₁ R₂ : X → ℝ) (x : X) : ℝ :=
  stabilityError (R₁ x) (R₂ x) +
    CurrentAssembly.assembledBlockError (r x)
      (blockDelta (entryEnergyError (err x))) (spanError x)

lemma compatibilityTotalError_eq {X : Type*}
    (r : X → ℕ) (spanError err R₁ R₂ countLoss : X → ℝ) (x : X) :
    compatibilityTotalError r spanError err R₁ R₂ countLoss x =
      baseTotalError r spanError err R₁ R₂ x + 2 * countLoss x := by
  unfold compatibilityTotalError baseTotalError effectiveTraceError stabilityError
  ring

/-- Build the filter-level capstone contract from an explicit little-o
estimate.  This is the intended seam for the independently developed Gram,
span, moment, and deletion lanes: they may first prove that their combined
error is `o(N)`, without knowing the final numerical epsilon requested by the
capstone. -/
def LossyAsymptoticEntrywiseInputs.ofLittleO
    {X : Type*} {l : Filter X}
    (r : X → ℕ) (N spanError err R₁ R₂ countLoss : X → ℝ)
    (countLoss_nonneg : ∀ x, 0 ≤ countLoss x)
    (eventuallyAnalytic : ∀ᶠ x in l, ∃ d b : ℕ,
      Nonempty (LossyFiniteEntrywiseAnalyticInputs d (r x) b
        (N x) (spanError x) (err x) (R₁ x) (R₂ x) (countLoss x)))
    (N_eventually_nonneg : ∀ᶠ x in l, 0 ≤ N x)
    (baseErrorsLittleO : baseTotalError r spanError err R₁ R₂ =o[l] N)
    (deletionLossLittleO : countLoss =o[l] N) :
    LossyAsymptoticEntrywiseInputs l where
  r := r
  N := N
  spanError := spanError
  err := err
  R₁ := R₁
  R₂ := R₂
  countLoss := countLoss
  countLoss_nonneg := countLoss_nonneg
  eventuallyAnalytic := eventuallyAnalytic
  errorsAreSmall := by
    intro eta heta
    have errorsLittleO :
        compatibilityTotalError r spanError err R₁ R₂ countLoss =o[l] N := by
      have hsum := baseErrorsLittleO.add (deletionLossLittleO.const_mul_left 2)
      have heq : compatibilityTotalError r spanError err R₁ R₂ countLoss =
          fun x => baseTotalError r spanError err R₁ R₂ x + 2 * countLoss x :=
        funext (compatibilityTotalError_eq r spanError err R₁ R₂ countLoss)
      rw [heq]
      exact hsum
    have hcoeff : 0 < (1 - Current.R / (Current.m : ℝ)) * eta :=
      mul_pos Current.one_sub_R_div_m_pos heta
    have hsmall := isLittleO_iff.mp errorsLittleO hcoeff
    filter_upwards [hsmall, N_eventually_nonneg] with x hx hN
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN] at hx
    exact (le_abs_self (compatibilityTotalError r spanError err R₁ R₂ countLoss x)).trans hx

/-- Compatibility constructor into the already-audited asymptotic entrywise
interface.  Its count field is explicitly `effectiveCount`; no identification
with the true zero count is made. -/
def LossyAsymptoticEntrywiseInputs.toEntrywise
    {X : Type*} {l : Filter X} (h : LossyAsymptoticEntrywiseInputs l) :
    AsymptoticEntrywiseAnalyticInputs l where
  r := h.r
  N := fun x => effectiveCount (h.N x) (h.countLoss x)
  spanError := h.spanError
  err := h.err
  R₁ := fun x => effectiveTraceError (h.R₁ x) (h.countLoss x)
  R₂ := h.R₂
  eventuallyAnalytic := by
    filter_upwards [h.eventuallyAnalytic] with x hx
    obtain ⟨d, b, hx⟩ := hx
    exact ⟨d, b, hx.map LossyFiniteEntrywiseAnalyticInputs.toFiniteEntrywiseAnalyticInputs⟩
  errorsAreSmall := by
    intro eta heta
    filter_upwards [h.errorsAreSmall eta heta] with x hx
    have hcoeff : 0 ≤ (1 - Current.R / (Current.m : ℝ)) * eta :=
      mul_nonneg Current.one_sub_R_div_m_pos.le heta.le
    have hNle : h.N x ≤ effectiveCount (h.N x) (h.countLoss x) := by
      unfold effectiveCount
      linarith [h.countLoss_nonneg x]
    exact hx.trans (mul_le_mul_of_nonneg_left hNle hcoeff)

/-- Mockable end-to-end target theorem.  Independent lanes need only populate
`LossyAsymptoticEntrywiseInputs`; the compatibility conversion and the final
removal of the artificial effective-count surplus are proved here. -/
theorem LossyAsymptoticEntrywiseInputs.target
    {X : Type*} {l : Filter X} (h : LossyAsymptoticEntrywiseInputs l) :
    ∀ᶠ x in l, Current.target * h.N x ≤ (h.r x : ℝ) := by
  have heff := h.toEntrywise.target
  filter_upwards [heff] with x hx
  have hNle : h.N x ≤ effectiveCount (h.N x) (h.countLoss x) := by
    unfold effectiveCount
    linarith [h.countLoss_nonneg x]
  exact (mul_le_mul_of_nonneg_left hNle Current.target_pos.le).trans hx

/-- Mocked end-to-end constructor directly from the semantic finite data and
an `o(N)` error proof.  This theorem is useful as an integration gate before
the individual analytic producers have been completed. -/
theorem target_of_littleO
    {X : Type*} {l : Filter X}
    (r : X → ℕ) (N spanError err R₁ R₂ countLoss : X → ℝ)
    (countLoss_nonneg : ∀ x, 0 ≤ countLoss x)
    (eventuallyAnalytic : ∀ᶠ x in l, ∃ d b : ℕ,
      Nonempty (LossyFiniteEntrywiseAnalyticInputs d (r x) b
        (N x) (spanError x) (err x) (R₁ x) (R₂ x) (countLoss x)))
    (N_eventually_nonneg : ∀ᶠ x in l, 0 ≤ N x)
    (baseErrorsLittleO : baseTotalError r spanError err R₁ R₂ =o[l] N)
    (deletionLossLittleO : countLoss =o[l] N) :
    ∀ᶠ x in l, Current.target * N x ≤ (r x : ℝ) :=
  (LossyAsymptoticEntrywiseInputs.ofLittleO r N spanError err R₁ R₂ countLoss
    countLoss_nonneg eventuallyAnalytic N_eventually_nonneg
    baseErrorsLittleO deletionLossLittleO).target

end Zeta23Ext.CurrentRetainedWithLoss
