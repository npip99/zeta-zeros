/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.RationalTrigCell
import Zeta23Ext.CurrentWindow

/-!
# Exact rational range reduction for current-window arguments

Generated trigonometric rows should not contain hand-written proofs that an
argument lies in its `k*pi` Taylor cell.  This module implements a small
rational interval evaluator and proves its semantics once.  Concrete rows can
thereafter discharge range reduction with `by decide`.
-/

noncomputable section

open Real

namespace Zeta23Ext.CurrentWindowArgumentReduction

/-- A closed interval with rational endpoints. -/
structure QInterval where
  lo : ℚ
  hi : ℚ

def QInterval.Mem (I : QInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def QInterval.add (I J : QInterval) : QInterval :=
  ⟨I.lo + J.lo, I.hi + J.hi⟩

def QInterval.neg (I : QInterval) : QInterval :=
  ⟨-I.hi, -I.lo⟩

def QInterval.sub (I J : QInterval) : QInterval := I.add J.neg

/-- Scalar interval multiplication, with endpoint reversal for negative
scalars handled by the executable definition. -/
def QInterval.smul (q : ℚ) (I : QInterval) : QInterval :=
  if 0 ≤ q then ⟨q * I.lo, q * I.hi⟩ else ⟨q * I.hi, q * I.lo⟩

lemma QInterval.mem_add {I J : QInterval} {x y : ℝ}
    (hx : I.Mem x) (hy : J.Mem y) : (I.add J).Mem (x + y) := by
  exact ⟨by exact_mod_cast add_le_add hx.1 hy.1,
    by exact_mod_cast add_le_add hx.2 hy.2⟩

lemma QInterval.mem_neg {I : QInterval} {x : ℝ} (hx : I.Mem x) :
    I.neg.Mem (-x) := by
  exact ⟨by exact_mod_cast neg_le_neg hx.2,
    by exact_mod_cast neg_le_neg hx.1⟩

lemma QInterval.mem_sub {I J : QInterval} {x y : ℝ}
    (hx : I.Mem x) (hy : J.Mem y) : QInterval.Mem (QInterval.sub I J) (x - y) := by
  simpa [sub_eq_add_neg, QInterval.sub] using
    QInterval.mem_add hx (QInterval.mem_neg hy)

lemma QInterval.mem_smul {I : QInterval} {x : ℝ} (hx : I.Mem x)
    (q : ℚ) : (I.smul q).Mem ((q : ℝ) * x) := by
  unfold QInterval.smul
  split_ifs with hq
  · constructor
    · change ((q * I.lo : ℚ) : ℝ) ≤ (q : ℝ) * x
      norm_num only [Rat.cast_mul]
      exact mul_le_mul_of_nonneg_left hx.1 (by exact_mod_cast hq)
    · change (q : ℝ) * x ≤ ((q * I.hi : ℚ) : ℝ)
      norm_num only [Rat.cast_mul]
      exact mul_le_mul_of_nonneg_left hx.2 (by exact_mod_cast hq)
  · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hq)
    constructor
    · change ((q * I.hi : ℚ) : ℝ) ≤ (q : ℝ) * x
      norm_num only [Rat.cast_mul]
      exact mul_le_mul_of_nonpos_left hx.2 hq'
    · change (q : ℝ) * x ≤ ((q * I.lo : ℚ) : ℝ)
      norm_num only [Rat.cast_mul]
      exact mul_le_mul_of_nonpos_left hx.1 hq'

def piInterval : QInterval :=
  ⟨314159265358979323846 / 10 ^ 20,
    314159265358979323847 / 10 ^ 20⟩

def sqrtTwoInterval : QInterval := ⟨707 / 500, 283 / 200⟩

lemma pi_mem : piInterval.Mem Real.pi := by
  unfold piInterval QInterval.Mem
  simpa using ⟨TranscendentalBounds.pi_rational_bounds.1.le,
    TranscendentalBounds.pi_rational_bounds.2.le⟩

lemma sqrtTwo_mem : sqrtTwoInterval.Mem (Real.sqrt 2) :=
  by simpa [sqrtTwoInterval, QInterval.Mem] using
    TranscendentalBounds.sqrt_two_bounds

/-- Rational enclosure of `frequency j * x - k*pi` for a rational centre
`x`.  The periodic frequencies collapse to one rational multiple of `pi`;
the algebraic frequency uses independent `sqrt 2` and `pi` intervals. -/
def argumentInterval (j : Fin 7) (x : ℚ) (k : ℤ) : QInterval :=
  if (j : ℕ) = 0 then
    (sqrtTwoInterval.smul x).sub (piInterval.smul k)
  else
    piInterval.smul (2 * (j : ℕ) * x - k)

lemma argument_mem (j : Fin 7) (x : ℚ) (k : ℤ) :
    (argumentInterval j x k).Mem
      (CurrentWindow.frequency j * (x : ℝ) - (k : ℝ) * Real.pi) := by
  unfold argumentInterval
  split_ifs with hj
  · have hj0 : j = 0 := Fin.ext (by simpa using hj)
    subst j
    simpa [CurrentWindow.frequency, mul_comm] using
      QInterval.mem_sub (QInterval.mem_smul sqrtTwo_mem x)
        (QInterval.mem_smul pi_mem (k : ℚ))
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (j : ℕ) = m + 1 := by
      use (j : ℕ) - 1
      omega
    have hfreq : CurrentWindow.frequency j = 2 * Real.pi * (j : ℕ) := by
      rcases j with ⟨_ | m, hmj⟩
      · simp at hj
      · simp [CurrentWindow.frequency]
    rw [hfreq]
    have h := QInterval.mem_smul pi_mem (2 * (j : ℕ) * x - (k : ℚ))
    convert h using 1 <;> norm_num <;> ring

/-- Boolean inclusion check saying the computed argument interval lies in the
Taylor witness cell. -/
def reductionCheck (j : Fin 7) (x : ℚ)
    (w : RationalTrigCell.Witness) : Bool :=
  decide ((w.center - w.radius ≤ (argumentInterval j x w.k).lo) ∧
    ((argumentInterval j x w.k).hi ≤ w.center + w.radius))

lemma reductionCheck_sound {j : Fin 7} {x : ℚ}
    {w : RationalTrigCell.Witness} (h : reductionCheck j x w = true) :
    |(CurrentWindow.frequency j * (x : ℝ) - (w.k : ℝ) * Real.pi) -
      (w.center : ℝ)| ≤ (w.radius : ℝ) := by
  have hinc : w.center - w.radius ≤ (argumentInterval j x w.k).lo ∧
      (argumentInterval j x w.k).hi ≤ w.center + w.radius := by
    simpa [reductionCheck] using of_decide_eq_true h
  have hmem := argument_mem j x w.k
  rw [abs_le]
  have hincR : (w.center - w.radius : ℚ) ≤
        (argumentInterval j x w.k).lo ∧
      (argumentInterval j x w.k).hi ≤ (w.center + w.radius : ℚ) := hinc
  have hloRat : ((w.center - w.radius : ℚ) : ℝ) ≤
      ((argumentInterval j x w.k).lo : ℝ) := by exact_mod_cast hincR.1
  have hhiRat : ((argumentInterval j x w.k).hi : ℝ) ≤
      ((w.center + w.radius : ℚ) : ℝ) := by exact_mod_cast hincR.2
  have hlo : ((w.center : ℝ) - (w.radius : ℝ)) ≤
      CurrentWindow.frequency j * (x : ℝ) - (w.k : ℝ) * Real.pi := by
    norm_num only [Rat.cast_sub] at hloRat
    exact hloRat.trans hmem.1
  have hhi : CurrentWindow.frequency j * (x : ℝ) - (w.k : ℝ) * Real.pi ≤
      (w.center : ℝ) + (w.radius : ℝ) := by
    norm_num only [Rat.cast_add] at hhiRat
    exact hmem.2.trans hhiRat
  constructor <;> linarith

end Zeta23Ext.CurrentWindowArgumentReduction
