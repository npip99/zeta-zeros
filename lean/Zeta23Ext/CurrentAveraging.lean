/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentBlockMatrix
import Zeta23Ext.Bridge

/-!
# Offset averaging for the current block reward

This is the exact finite combinatorial seam after the single-block theorem.
It reuses the established offset partition, pinching, block-count, and span
bookkeeping from `Zeta23Ext.Bridge`.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Matrix Finset
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.CurrentAveraging

open Zeta23Ext
open Zeta23Ext.Aggregation
open Zeta23Ext.Stability

/-! ## Generic exact averaging -/

/-- **Offset-averaged defect from a uniform full-block reward.**

For every full consecutive block of length `m`, assume

`reward - blockLoss ≤ blockTracePsi + spanCoeff * blockSpan`.

Then the exact finite bound is

`r*reward - (m-1)*reward - r*blockLoss
  - spanCoeff*(m-1)*totalSpan ≤ m*globalTracePsi`.

Thus the only endpoint loss is `(m-1)*reward`, the per-block loss is charged
at most `r` times, and every gap contributes to at most `m-1` block spans.
-/
theorem averaged_defect_of_block_bounds
    {r m : ℕ} (hm : 1 ≤ m) (hr : 0 < r)
    {reward blockLoss spanCoeff : ℝ}
    (hreward0 : 0 ≤ reward) (hloss0 : 0 ≤ blockLoss)
    (hlossReward : blockLoss ≤ reward) (hcoeff0 : 0 ≤ spanCoeff)
    {y : Fin r → ℝ} (hy : StrictMono y)
    {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosSemidef)
    (hblock : ∀ {K t : ℕ} (hKt : t + K * m ≤ r) (c : Fin K),
      reward - blockLoss ≤
        ∑ i, Psi ((hG.submatrix (blockEmb hKt c)).1.eigenvalues i) +
          spanCoeff *
            (y (blockEmb hKt c ⟨m - 1, by omega⟩) -
              y (blockEmb hKt c ⟨0, by omega⟩)) ) :
    (r : ℝ) * reward - ((m : ℝ) - 1) * reward
        - (r : ℝ) * blockLoss
        - spanCoeff * ((m : ℝ) - 1) *
          (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩)
      ≤ (m : ℝ) * ∑ j, Psi (hG.1.eigenvalues j) := by
  have hm0 : 0 < m := by omega
  have hspan0 : 0 ≤ y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩ := by
    refine sub_nonneg.mpr (hy.monotone ?_)
    change (0 : ℕ) ≤ r - 1
    omega
  have hDelta0 : 0 ≤ ∑ j, Psi (hG.1.eigenvalues j) :=
    Finset.sum_nonneg fun j _ => Psi_nonneg _
  by_cases hmr : r < m
  · have hrm : (r : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hmr
    have hrewardTerm :
        (r : ℝ) * reward - ((m : ℝ) - 1) * reward ≤ 0 := by
      nlinarith
    have hlossTerm : 0 ≤ (r : ℝ) * blockLoss := by positivity
    have hspanTerm : 0 ≤ spanCoeff * ((m : ℝ) - 1) *
        (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩) := by
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      positivity
    have hright : 0 ≤ (m : ℝ) * ∑ j, Psi (hG.1.eigenvalues j) := by
      positivity
    linarith
  push Not at hmr
  set Y : ℕ → ℝ := fun n => y ⟨min n (r - 1), by omega⟩ with hYdef
  have hY : Monotone Y := by
    intro a b hab
    refine hy.monotone ?_
    rw [Fin.le_def]
    simp only
    omega
  have hYval : ∀ j : Fin r, Y (j : ℕ) = y j := by
    intro j
    have hj := j.isLt
    show y _ = y j
    congr 1
    apply Fin.ext
    simp only
    omega
  set Delta : ℝ := ∑ j, Psi (hG.1.eigenvalues j) with hDeltadef
  have hoff : ∀ t ∈ Finset.range m,
      ((r - t) / m : ℕ) * (reward - blockLoss)
        - spanCoeff * ∑ c ∈ Finset.range ((r - t) / m),
            (Y (t + c * m + (m - 1)) - Y (t + c * m))
      ≤ Delta := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hKt : t + ((r - t) / m) * m ≤ r := by
      have hdiv : (r - t) / m * m ≤ r - t := Nat.div_mul_le_self _ _
      omega
    set K : ℕ := (r - t) / m with hKdef
    have hpin := pinching_runs hm0 hKt hG
    have hblocks : ∀ c : Fin K,
        reward - blockLoss - spanCoeff *
            (Y (t + (c : ℕ) * m + (m - 1)) - Y (t + (c : ℕ) * m))
          ≤ ∑ i, Psi ((hG.submatrix (blockEmb hKt c)).1.eigenvalues i) := by
      intro c
      have hb := hblock hKt c
      have he1 : y (blockEmb hKt c ⟨m - 1, by omega⟩) =
          Y (t + (c : ℕ) * m + (m - 1)) :=
        (hYval (blockEmb hKt c ⟨m - 1, by omega⟩)).symm
      have he0 : y (blockEmb hKt c ⟨0, by omega⟩) =
          Y (t + (c : ℕ) * m) := by
        have h := (hYval (blockEmb hKt c ⟨0, by omega⟩)).symm
        rw [h]
        congr 1
      rw [he1, he0] at hb
      linarith
    have hsum := Finset.sum_le_sum
      (fun c (_ : c ∈ (Finset.univ : Finset (Fin K))) => hblocks c)
    have hLHS : ∑ c : Fin K,
        (reward - blockLoss - spanCoeff *
          (Y (t + (c : ℕ) * m + (m - 1)) - Y (t + (c : ℕ) * m)))
        = (K : ℝ) * (reward - blockLoss)
          - spanCoeff * ∑ c ∈ Finset.range K,
              (Y (t + c * m + (m - 1)) - Y (t + c * m)) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun c => reward - blockLoss - spanCoeff *
          (Y (t + c * m + (m - 1)) - Y (t + c * m))) K]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.mul_comm]
      ring
    rw [hLHS] at hsum
    exact le_trans hsum hpin
  have hsum := Finset.sum_le_sum hoff
  have hRHS : ∑ _t ∈ Finset.range m, Delta = (m : ℝ) * Delta := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hLHS : ∑ t ∈ Finset.range m,
      (((r - t) / m : ℕ) * (reward - blockLoss)
        - spanCoeff * ∑ c ∈ Finset.range ((r - t) / m),
            (Y (t + c * m + (m - 1)) - Y (t + c * m)))
      = (∑ t ∈ Finset.range m, ((r - t) / m : ℕ) : ℝ) * (reward - blockLoss)
        - spanCoeff * ∑ t ∈ Finset.range m,
            ∑ c ∈ Finset.range ((r - t) / m),
              (Y (t + c * m + (m - 1)) - Y (t + c * m)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hRHS, hLHS] at hsum
  have hcount : (r : ℝ) + 1 - (m : ℝ) ≤
      (∑ t ∈ Finset.range m, ((r - t) / m : ℕ) : ℝ) := by
    have h := sum_blocks_ge hm0 hmr
    have hcast : ((r + 1 - m : ℕ) : ℝ) = (r : ℝ) + 1 - (m : ℝ) := by
      have hmle : m ≤ r + 1 := by omega
      push_cast [Nat.cast_sub hmle]
      ring
    calc
      (r : ℝ) + 1 - (m : ℝ) = ((r + 1 - m : ℕ) : ℝ) := hcast.symm
      _ ≤ ((∑ t ∈ Finset.range m, (r - t) / m : ℕ) : ℝ) := by
        exact_mod_cast h
      _ = (∑ t ∈ Finset.range m, ((r - t) / m : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
  have hrewardLoss : 0 ≤ reward - blockLoss := sub_nonneg.mpr hlossReward
  have hcountMul : ((r : ℝ) + 1 - (m : ℝ)) * (reward - blockLoss) ≤
      (∑ t ∈ Finset.range m, ((r - t) / m : ℕ) : ℝ) *
        (reward - blockLoss) :=
    mul_le_mul_of_nonneg_right hcount hrewardLoss
  have hspans := sum_spans_le hm (r := r) hY
  have hYr : Y (r - 1) = y ⟨r - 1, by omega⟩ := hYval ⟨r - 1, by omega⟩
  have hY0 : Y 0 = y ⟨0, hr⟩ := hYval ⟨0, hr⟩
  rw [hYr, hY0] at hspans
  have hspanMul : spanCoeff *
      (∑ t ∈ Finset.range m, ∑ c ∈ Finset.range ((r - t) / m),
        (Y (t + c * m + (m - 1)) - Y (t + c * m)))
      ≤ spanCoeff * (((m : ℝ) - 1) *
        (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩)) :=
    mul_le_mul_of_nonneg_left hspans hcoeff0
  have hlossEndpoint : 0 ≤ ((m : ℝ) - 1) * blockLoss := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    positivity
  have hexpand : ((r : ℝ) + 1 - (m : ℝ)) * (reward - blockLoss) =
      (r : ℝ) * reward - ((m : ℝ) - 1) * reward
        - (r : ℝ) * blockLoss + ((m : ℝ) - 1) * blockLoss := by
    ring
  have hfinite :
      (r : ℝ) * reward - ((m : ℝ) - 1) * reward
        - (r : ℝ) * blockLoss
        - spanCoeff * ((m : ℝ) - 1) *
          (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩)
      ≤ (m : ℝ) * Delta := by
    linarith [hsum, hcountMul, hspanMul]
  simpa [hDeltadef] using hfinite

/-! ## Exact current-result specialization -/

/-- Exact finite offset-average at `m=250`.  The loss `eta*delta` is charged
once per possible full block (bounded by `r`), while the endpoint loss is
exactly `249*R`. -/
theorem current_averaged_defect
    {r : ℕ} (hr : 0 < r) {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : Current.eta * delta ≤ Current.R)
    {y : Fin r → ℝ} (hy : StrictMono y)
    {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosSemidef)
    (hblock : ∀ {K t : ℕ} (hKt : t + K * Current.m ≤ r) (c : Fin K),
      Current.R - Current.eta * delta ≤
        ∑ i, Psi ((hG.submatrix (blockEmb hKt c)).1.eigenvalues i) +
          Current.eta * Current.pressureCap *
            (y (blockEmb hKt c ⟨Current.m - 1, by norm_num [Current.m]⟩) -
              y (blockEmb hKt c ⟨0, by norm_num [Current.m]⟩))) :
    (r : ℝ) * Current.R - 249 * Current.R
        - (r : ℝ) * (Current.eta * delta)
        - Current.eta * Current.pressureCap * 249 *
          (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩)
      ≤ 250 * ∑ j, Psi (hG.1.eigenvalues j) := by
  have h := averaged_defect_of_block_bounds (m := Current.m)
    (by norm_num [Current.m]) hr Current.R_pos.le
    (mul_nonneg Current.eta_pos.le hdelta0) hdelta
    (mul_nonneg Current.eta_pos.le Current.pressureCap_pos.le)
    hy hG hblock
  norm_num [Current.m] at h ⊢
  exact h

/-- Division by `250`, in the form used directly by an asymptotic counting
argument.  Every finite loss remains visible. -/
theorem current_averaged_defect_normalized
    {r : ℕ} (hr : 0 < r) {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : Current.eta * delta ≤ Current.R)
    {y : Fin r → ℝ} (hy : StrictMono y)
    {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosSemidef)
    (hblock : ∀ {K t : ℕ} (hKt : t + K * Current.m ≤ r) (c : Fin K),
      Current.R - Current.eta * delta ≤
        ∑ i, Psi ((hG.submatrix (blockEmb hKt c)).1.eigenvalues i) +
          Current.eta * Current.pressureCap *
            (y (blockEmb hKt c ⟨Current.m - 1, by norm_num [Current.m]⟩) -
              y (blockEmb hKt c ⟨0, by norm_num [Current.m]⟩))) :
    (Current.R / 250) * (r : ℝ) - (249 / 250) * Current.R
        - (Current.eta * delta / 250) * (r : ℝ)
        - Current.eta * Current.pressureCap * (249 / 250) *
          (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩)
      ≤ ∑ j, Psi (hG.1.eigenvalues j) := by
  have h := current_averaged_defect hr hdelta0 hdelta hy hG hblock
  nlinarith

end Zeta23Ext.CurrentAveraging
