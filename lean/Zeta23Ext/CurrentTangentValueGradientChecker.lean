/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWeightD2CellChecker
import Zeta23Ext.CurrentTangentCurrentAssembly

/-!
# Executable center-value and gradient witnesses

A tangent leaf evaluates the current objective at one rational six-gap center.
This module assigns one checked current-kernel cell to each of its 21 pair
spans, reuses that cell's value/first-derivative intervals, and checks the
resulting `F6` value and six coordinate-gradient intervals exactly over `Rat`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace Zeta23Ext.CurrentTangentValueGradientChecker

open CurrentWeightD2CellChecker
open Zeta23Ext.VerifiedCertificate.CurrentReplay

abbrev QInterval := CurrentWeightD2CellChecker.QInterval

def singleton (q : ℚ) : QInterval := ⟨q, q⟩

def qsumFinset {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → QInterval) : QInterval :=
  ⟨∑ i ∈ s, (f i).lo, ∑ i ∈ s, (f i).hi⟩

lemma QInterval.mem_sumFinset {α : Type*} [DecidableEq α]
    {s : Finset α} {f : α → QInterval} {g : α → ℝ}
    (h : ∀ i ∈ s, (f i).Mem (g i)) :
    (qsumFinset s f).Mem (∑ i ∈ s, g i) := by
  unfold qsumFinset CurrentWindowArgumentReduction.QInterval.Mem
  constructor
  · change ((∑ i ∈ s, (f i).lo : ℚ) : ℝ) ≤ ∑ i ∈ s, g i
    push_cast
    exact Finset.sum_le_sum fun i hi => (h i hi).1
  · change (∑ i ∈ s, g i) ≤ ((∑ i ∈ s, (f i).hi : ℚ) : ℝ)
    push_cast
    exact Finset.sum_le_sum fun i hi => (h i hi).2

def pressureQ : ℚ := 1 / 2300
def pairWeightQ (i j : ℕ) : ℚ :=
  (Weighted.pairWeightNumerator i j : ℚ) / 1000000

lemma pressureQ_cast : (pressureQ : ℝ) = Weighted.pressure := by
  norm_num [pressureQ, Weighted.pressure]

lemma pairWeightQ_cast (i j : ℕ) :
    (pairWeightQ i j : ℝ) = Weighted.pairWeight i j := by
  simp [pairWeightQ, Weighted.pairWeight]

def centerNat (center : Fin 6 → ℚ) (i : ℕ) : ℚ :=
  if hi : i < 6 then center ⟨i, hi⟩ else 0

def spanQ (center : Fin 6 → ℚ) (i r : ℕ) : ℚ :=
  ∑ t ∈ Finset.Ico i (i + r), centerNat center t

private lemma realSpan_center_eq (center : Fin 6 → ℚ) (i r : ℕ) :
    realSpan (fun k => (center k : ℝ)) i r = (spanQ center i r : ℝ) := by
  unfold realSpan spanQ centerNat Aggregation.gext
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  split_ifs with ht
  · rfl
  · norm_num

/-- The current-kernel cell assigned to one pair span. -/
structure SpanWitness where
  kernel : CurrentWeightD2CellChecker.CellWitness

def SpanWitness.check (w : SpanWitness) (center : Fin 6 → ℚ)
    (i r : ℕ) : Bool :=
  w.kernel.check && decide (1 ≤ r ∧ i + r ≤ 6 ∧
    (w.kernel.cell : ℚ) / 4000 ≤ spanQ center i r ∧
    spanQ center i r ≤ (w.kernel.cell + 1 : ℕ) / 4000)

private lemma span_check_facts {w : SpanWitness} {center : Fin 6 → ℚ}
    {i r : ℕ} (h : w.check center i r = true) :
    w.kernel.check = true ∧ 1 ≤ r ∧ i + r ≤ 6 ∧
      (w.kernel.cell : ℚ) / 4000 ≤ spanQ center i r ∧
      spanQ center i r ≤ (w.kernel.cell + 1 : ℕ) / 4000 := by
  rw [SpanWitness.check, Bool.and_eq_true] at h
  exact ⟨h.1, of_decide_eq_true h.2⟩

theorem SpanWitness.sound {w : SpanWitness} {center : Fin 6 → ℚ}
    {i r : ℕ} (h : w.check center i r = true) :
    (weightInterval w.kernel.minus w.kernel.plus).Mem
        (CurrentWindow.weight (realSpan (fun k => (center k : ℝ)) i r)) ∧
    (weightD1Interval w.kernel.minus w.kernel.plus).Mem
        (CurrentKernelTotalDerivatives.closedWeightD1Total
          (realSpan (fun k => (center k : ℝ)) i r)) := by
  have hf := span_check_facts h
  apply w.kernel.value_first_sound hf.1
  rw [realSpan_center_eq]
  have hlo : ((w.kernel.cell : ℚ) / 4000 : ℝ) ≤ (spanQ center i r : ℝ) := by
    have hc : ((((w.kernel.cell : ℕ) : ℚ) / 4000 : ℚ) : ℝ) ≤
        (spanQ center i r : ℝ) := Rat.cast_le.mpr hf.2.2.2.1
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc
  have hhi : (spanQ center i r : ℝ) ≤
      ((w.kernel.cell + 1 : ℕ) : ℝ) / 4000 := by
    have hc : (spanQ center i r : ℝ) ≤
        (((((w.kernel.cell + 1 : ℕ) : ℚ) / 4000 : ℚ)) : ℝ) :=
      Rat.cast_le.mpr hf.2.2.2.2
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc
  norm_num only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hlo hhi ⊢
  exact ⟨hlo, hhi⟩

def objectiveInterval (center : Fin 6 → ℚ)
    (span : ℕ → ℕ → SpanWitness) : QInterval :=
  (singleton (pressureQ * ∑ i, center i)).add
    (qsumFinset (Finset.Icc 1 6) fun r =>
      qsumFinset (Finset.range (7 - r)) fun i =>
        ((weightInterval (span i r).kernel.minus
          (span i r).kernel.plus).smul (pairWeightQ i (i + r))))

def gradientInterval (center : Fin 6 → ℚ)
    (span : ℕ → ℕ → SpanWitness) (k : Fin 6) : QInterval :=
  (singleton pressureQ).add
    (qsumFinset (Finset.Icc 1 6) fun r =>
      qsumFinset (Finset.range (7 - r)) fun i =>
        if k.val ∈ Finset.Ico i (i + r) then
          (weightD1Interval (span i r).kernel.minus
            (span i r).kernel.plus).smul (pairWeightQ i (i + r))
        else singleton 0)

/-- Data-only checker for one tangent center.  `reportedValue` and
`reportedGradient` are the intervals copied into the tangent payload. -/
structure Witness where
  center : Fin 6 → ℚ
  span : ℕ → ℕ → SpanWitness
  reportedValue : QInterval
  reportedGradient : Fin 6 → QInterval

noncomputable def Witness.Check (w : Witness) : Prop :=
    (∀ r ∈ Finset.Icc (1 : ℕ) 6, ∀ i ∈ Finset.range (7 - r),
      (w.span i r).check w.center i r = true) ∧
    w.reportedValue.lo ≤ (objectiveInterval w.center w.span).lo ∧
    (objectiveInterval w.center w.span).hi ≤ w.reportedValue.hi ∧
    (∀ k, (w.reportedGradient k).lo ≤ (gradientInterval w.center w.span k).lo ∧
      (gradientInterval w.center w.span k).hi ≤ (w.reportedGradient k).hi)

noncomputable def Witness.check (w : Witness) : Bool := by
  classical
  exact decide w.Check

private lemma check_facts {w : Witness} (h : w.check = true) :
    (∀ r ∈ Finset.Icc (1 : ℕ) 6, ∀ i ∈ Finset.range (7 - r),
      (w.span i r).check w.center i r = true) ∧
    w.reportedValue.lo ≤ (objectiveInterval w.center w.span).lo ∧
    (objectiveInterval w.center w.span).hi ≤ w.reportedValue.hi ∧
    (∀ k, (w.reportedGradient k).lo ≤ (gradientInterval w.center w.span k).lo ∧
      (gradientInterval w.center w.span k).hi ≤ (w.reportedGradient k).hi) := by
  classical
  have hc : w.Check := by
    exact of_decide_eq_true (show decide w.Check = true by
      simpa only [Witness.check] using h)
  exact hc

private theorem objective_interval_sound (w : Witness)
    (hs : ∀ r ∈ Finset.Icc (1 : ℕ) 6, ∀ i ∈ Finset.range (7 - r),
      (w.span i r).check w.center i r = true) :
    (objectiveInterval w.center w.span).Mem
      (Weighted.F6 CurrentWindow.weight (fun i => (w.center i : ℝ))) := by
  have hpairs : ∀ r ∈ Finset.Icc (1 : ℕ) 6, ∀ i ∈ Finset.range (7 - r),
      (weightInterval (w.span i r).kernel.minus
        (w.span i r).kernel.plus).Mem
      (CurrentWindow.weight (realSpan (fun k => (w.center k : ℝ))
        i r)) := fun r hr i hi => ((w.span i r).sound (hs r hr i hi)).1
  have hsum : (qsumFinset (Finset.Icc 1 6) fun r =>
      qsumFinset (Finset.range (7 - r)) fun i =>
      (weightInterval (w.span i r).kernel.minus
        (w.span i r).kernel.plus).smul (pairWeightQ i (i + r))).Mem
      (∑ r ∈ Finset.Icc (1 : ℕ) 6, ∑ i ∈ Finset.range (7 - r),
        Weighted.pairWeight i (i + r) *
          CurrentWindow.weight (realSpan (fun k => (w.center k : ℝ))
            i r)) := by
    apply QInterval.mem_sumFinset
    intro r hr
    apply QInterval.mem_sumFinset
    intro i hi
    have ht := CurrentWindowArgumentReduction.QInterval.mem_smul (hpairs r hr i hi)
      (pairWeightQ i (i + r))
    rw [pairWeightQ_cast] at ht
    simpa [mul_comm] using ht
  have hpressure : (singleton (pressureQ * ∑ i, w.center i)).Mem
      (Weighted.pressure * ∑ i, (w.center i : ℝ)) := by
    change ((pressureQ * ∑ i, w.center i : ℚ) : ℝ) ≤ _ ∧
      _ ≤ ((pressureQ * ∑ i, w.center i : ℚ) : ℝ)
    push_cast
    rw [pressureQ_cast]
    exact ⟨le_rfl, le_rfl⟩
  have hall := CurrentWindowArgumentReduction.QInterval.mem_add hpressure hsum
  change (objectiveInterval w.center w.span).Mem
    (Weighted.pressure * ∑ i, (w.center i : ℝ) +
      ∑ r ∈ Finset.Icc (1 : ℕ) 6, ∑ i ∈ Finset.range (7 - r),
        Weighted.pairWeight i (i + r) *
          CurrentWindow.weight (realSpan (fun k => (w.center k : ℝ)) i r))
  exact hall

private theorem gradient_interval_sound (w : Witness)
    (hs : ∀ r ∈ Finset.Icc (1 : ℕ) 6, ∀ i ∈ Finset.range (7 - r),
      (w.span i r).check w.center i r = true)
    (k : Fin 6) :
    (gradientInterval w.center w.span k).Mem
      (Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentAssembly.gradient
        (fun i => (w.center i : ℝ)) k) := by
  have hterm : ∀ r ∈ Finset.Icc (1 : ℕ) 6, ∀ i ∈ Finset.range (7 - r),
      (if k.val ∈ Finset.Ico i (i + r) then
        (weightD1Interval (w.span i r).kernel.minus
          (w.span i r).kernel.plus).smul
            (pairWeightQ i (i + r)) else singleton 0).Mem
      (if k.val ∈ Finset.Ico i (i + r) then
        Weighted.pairWeight i (i + r) *
          CurrentKernelTotalDerivatives.closedWeightD1Total
            (realSpan (fun j => (w.center j : ℝ)) i r) else 0) := by
    intro r hr i hi
    split_ifs with hk
    · have ht := CurrentWindowArgumentReduction.QInterval.mem_smul
        (((w.span i r).sound (hs r hr i hi)).2)
        (pairWeightQ i (i + r))
      rw [pairWeightQ_cast] at ht
      simpa [mul_comm] using ht
    · simp [singleton, CurrentWindowArgumentReduction.QInterval.Mem]
  have hsum := QInterval.mem_sumFinset fun r hr =>
    QInterval.mem_sumFinset fun i hi => hterm r hr i hi
  have hp : (singleton pressureQ).Mem Weighted.pressure := by
    change (pressureQ : ℝ) ≤ Weighted.pressure ∧
      Weighted.pressure ≤ (pressureQ : ℝ)
    rw [pressureQ_cast]
    exact ⟨le_rfl, le_rfl⟩
  have hall := CurrentWindowArgumentReduction.QInterval.mem_add hp hsum
  simpa [gradientInterval,
    Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentAssembly.gradient] using hall

/-- Checked center data encloses the exact current objective and canonical
coordinate gradient consumed by tangent semantics. -/
theorem Witness.sound (w : Witness) (h : w.check = true) :
    w.reportedValue.Mem
      (Weighted.F6 CurrentWindow.weight (fun i => (w.center i : ℝ))) ∧
    ∀ k, (w.reportedGradient k).Mem
      (Zeta23Ext.VerifiedCertificate.CurrentTangent.CurrentAssembly.gradient
        (fun i => (w.center i : ℝ)) k) := by
  have hf := check_facts h
  have hv := objective_interval_sound w hf.1
  constructor
  · have hlo : (w.reportedValue.lo : ℝ) ≤
        ((objectiveInterval w.center w.span).lo : ℝ) := by
      exact_mod_cast hf.2.1
    have hhi : ((objectiveInterval w.center w.span).hi : ℝ) ≤
        (w.reportedValue.hi : ℝ) := by
      exact_mod_cast hf.2.2.1
    exact ⟨hlo.trans hv.1, hv.2.trans hhi⟩
  · intro k
    have hg := gradient_interval_sound w hf.1 k
    have hlo : ((w.reportedGradient k).lo : ℝ) ≤
        ((gradientInterval w.center w.span k).lo : ℝ) := by
      exact_mod_cast (hf.2.2.2 k).1
    have hhi : ((gradientInterval w.center w.span k).hi : ℝ) ≤
        ((w.reportedGradient k).hi : ℝ) := by
      exact_mod_cast (hf.2.2.2 k).2
    exact ⟨hlo.trans hg.1, hg.2.trans hhi⟩

end Zeta23Ext.CurrentTangentValueGradientChecker
end
