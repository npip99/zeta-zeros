/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CheckedSincJet
import Zeta23Ext.NearZeroTotalSincJet
import Zeta23Ext.CurrentWindowClosedHAssembly

/-!
# Executable current-weight second-derivative cells

This is the generator-facing semantic format for a complete `w''` table row.
It combines fourteen ordinary/reflected or removable-point sinc jets, checks
their inclusion over one current grid cell, performs rational interval
arithmetic for `K`, `K'`, and `K''`, and checks a lower bound for the normalized
weight's genuine total second derivative.
-/

noncomputable section

open Real Set
open scoped BigOperators

namespace Zeta23Ext.CurrentWeightD2CellChecker

open CurrentWindowArgumentReduction
open CurrentKernelDerivatives
open CurrentKernelTotalDerivatives

abbrev QInterval := CurrentWindowArgumentReduction.QInterval

abbrev Valid (I : QInterval) : Prop := I.lo ≤ I.hi

def QInterval.mid (I : QInterval) : ℚ := (I.lo + I.hi) / 2
def QInterval.rad (I : QInterval) : ℚ := (I.hi - I.lo) / 2

def qmul (I J : QInterval) : QInterval :=
  let c := I.mid * J.mid
  let e := |I.mid| * J.rad + |J.mid| * I.rad + I.rad * J.rad
  ⟨c - e, c + e⟩

def qsum {n : ℕ} (f : Fin n → QInterval) : QInterval :=
  ⟨∑ i, (f i).lo, ∑ i, (f i).hi⟩

private lemma mem_mid_rad {I : QInterval} (hI : Valid I) {x : ℝ}
    (hx : I.Mem x) : |x - (I.mid : ℝ)| ≤ (I.rad : ℝ) := by
  rw [abs_le]
  have hcast : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast hI
  simp only [QInterval.mid, QInterval.rad]
  push_cast
  constructor <;> linarith [hx.1, hx.2]

lemma QInterval.valid_add {I J : QInterval} (hI : Valid I) (hJ : Valid J) :
    Valid (I.add J) := by
  exact add_le_add hI hJ

lemma QInterval.valid_neg {I : QInterval} (hI : Valid I) : Valid I.neg := by
  exact neg_le_neg hI

lemma QInterval.valid_sub {I J : QInterval} (hI : Valid I) (hJ : Valid J) :
    Valid (I.sub J) := QInterval.valid_add hI (QInterval.valid_neg hJ)

lemma QInterval.valid_smul {I : QInterval} (hI : Valid I) (q : ℚ) :
    Valid (I.smul q) := by
  unfold CurrentWindowArgumentReduction.QInterval.smul
  split_ifs with hq
  · exact mul_le_mul_of_nonneg_left hI hq
  · exact mul_le_mul_of_nonpos_left hI (le_of_not_ge hq)

lemma QInterval.valid_sum {n : ℕ} {f : Fin n → QInterval}
    (hf : ∀ i, Valid (f i)) : Valid (qsum f) := by
  unfold Valid qsum
  exact Finset.sum_le_sum fun i _ => hf i

lemma QInterval.mem_sum {n : ℕ} {f : Fin n → QInterval} {g : Fin n → ℝ}
    (h : ∀ i, (f i).Mem (g i)) : (qsum f).Mem (∑ i, g i) := by
  unfold qsum QInterval.Mem
  constructor
  · change ((∑ i, (f i).lo : ℚ) : ℝ) ≤ ∑ i, g i
    push_cast
    exact Finset.sum_le_sum fun i _ => (h i).1
  · change (∑ i, g i) ≤ ((∑ i, (f i).hi : ℚ) : ℝ)
    push_cast
    exact Finset.sum_le_sum fun i _ => (h i).2

lemma QInterval.valid_mul {I J : QInterval} (hI : Valid I) (hJ : Valid J) :
    Valid (qmul I J) := by
  change I.lo ≤ I.hi at hI
  change J.lo ≤ J.hi at hJ
  have hrI : 0 ≤ I.rad := by unfold QInterval.rad; linarith
  have hrJ : 0 ≤ J.rad := by unfold QInterval.rad; linarith
  unfold qmul Valid
  dsimp
  have : 0 ≤ |I.mid| * J.rad + |J.mid| * I.rad + I.rad * J.rad := by
    positivity
  linarith

lemma QInterval.mem_mul {I J : QInterval} (hI : Valid I) (hJ : Valid J)
    {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (qmul I J).Mem (x * y) := by
  change I.lo ≤ I.hi at hI
  change J.lo ≤ J.hi at hJ
  have hdx := mem_mid_rad hI hx
  have hdy := mem_mid_rad hJ hy
  have hrI : (0 : ℝ) ≤ I.rad := by
    exact_mod_cast (show (0 : ℚ) ≤ I.rad by unfold QInterval.rad; linarith)
  have hrJ : (0 : ℝ) ≤ J.rad := by
    exact_mod_cast (show (0 : ℚ) ≤ J.rad by unfold QInterval.rad; linarith)
  have he : |x * y - (I.mid : ℝ) * (J.mid : ℝ)| ≤
      |(I.mid : ℝ)| * (J.rad : ℝ) +
        |(J.mid : ℝ)| * (I.rad : ℝ) +
        (I.rad : ℝ) * (J.rad : ℝ) := by
    rw [show x * y - (I.mid : ℝ) * (J.mid : ℝ) =
      (I.mid : ℝ) * (y - J.mid) + (J.mid : ℝ) * (x - I.mid) +
        (x - I.mid) * (y - J.mid) by ring]
    calc
      _ ≤ |(I.mid : ℝ) * (y - J.mid)| +
          |(J.mid : ℝ) * (x - I.mid)| +
          |(x - I.mid) * (y - J.mid)| := by
            calc
              _ ≤ |(I.mid : ℝ) * (y - J.mid) +
                    (J.mid : ℝ) * (x - I.mid)| +
                  |(x - I.mid) * (y - J.mid)| := abs_add_le _ _
              _ ≤ (|(I.mid : ℝ) * (y - J.mid)| +
                    |(J.mid : ℝ) * (x - I.mid)|) +
                  |(x - I.mid) * (y - J.mid)| := by
                    gcongr; exact abs_add_le _ _
      _ = |(I.mid : ℝ)| * |y - J.mid| +
          |(J.mid : ℝ)| * |x - I.mid| +
          |x - I.mid| * |y - J.mid| := by simp only [abs_mul]
      _ ≤ |(I.mid : ℝ)| * (J.rad : ℝ) +
          |(J.mid : ℝ)| * (I.rad : ℝ) +
          (I.rad : ℝ) * (J.rad : ℝ) := by gcongr
  unfold qmul QInterval.Mem
  dsimp
  push_cast
  rw [abs_le] at he
  exact ⟨by linarith [he.1], by linarith [he.2]⟩

/-! ## Current-cell argument intervals -/

def xInterval (cell : ℕ) : QInterval :=
  ⟨(cell : ℚ) / 4000, (cell + 1 : ℕ) / 4000⟩

def piTimesXInterval (cell : ℕ) : QInterval :=
  ⟨piInterval.lo * (cell : ℚ) / 4000,
    piInterval.hi * (cell + 1 : ℕ) / 4000⟩

def frequencyInterval (j : Fin 7) : QInterval :=
  if (j : ℕ) = 0 then sqrtTwoInterval else piInterval.smul (2 * (j : ℕ))

def minusArgumentInterval (cell : ℕ) (j : Fin 7) : QInterval :=
  (frequencyInterval j).sub ((piTimesXInterval cell).smul 2) |>.smul (1 / 2)

def plusArgumentInterval (cell : ℕ) (j : Fin 7) : QInterval :=
  (frequencyInterval j).add ((piTimesXInterval cell).smul 2) |>.smul (1 / 2)

lemma xInterval_mem {cell : ℕ} {x : ℝ}
    (hx : x ∈ Icc ((cell : ℝ) / 4000) ((cell + 1 : ℕ) / 4000)) :
    (xInterval cell).Mem x := by simpa [xInterval, QInterval.Mem] using hx

private lemma piTimesXInterval_mem {cell : ℕ} {x : ℝ}
    (hx : x ∈ Icc ((cell : ℝ) / 4000) ((cell + 1 : ℕ) / 4000)) :
    (piTimesXInterval cell).Mem (Real.pi * x) := by
  have hp := pi_mem
  have hx0 : 0 ≤ x := le_trans (by positivity) hx.1
  have hlo0 : (0 : ℝ) ≤ (cell : ℝ) / 4000 := by positivity
  have hhi0 : (0 : ℝ) ≤ ((cell + 1 : ℕ) : ℝ) / 4000 := by positivity
  constructor
  · change ((piInterval.lo * (cell : ℚ) / 4000 : ℚ) : ℝ) ≤ Real.pi * x
    push_cast
    calc
      (piInterval.lo : ℝ) * (cell : ℝ) / 4000 =
          (piInterval.lo : ℝ) * ((cell : ℝ) / 4000) := by ring
      _ ≤ Real.pi * ((cell : ℝ) / 4000) :=
        mul_le_mul_of_nonneg_right hp.1 hlo0
      _ ≤ Real.pi * x := mul_le_mul_of_nonneg_left hx.1 Real.pi_pos.le
  · change Real.pi * x ≤
      ((piInterval.hi * (cell + 1 : ℕ) / 4000 : ℚ) : ℝ)
    push_cast
    calc
      Real.pi * x ≤ Real.pi * (((cell + 1 : ℕ) : ℝ) / 4000) :=
        mul_le_mul_of_nonneg_left hx.2 Real.pi_pos.le
      _ ≤ (piInterval.hi : ℝ) * (((cell + 1 : ℕ) : ℝ) / 4000) :=
        mul_le_mul_of_nonneg_right hp.2 hhi0
      _ = (piInterval.hi : ℝ) * ((cell : ℝ) + 1) / 4000 := by
        norm_num; ring

private lemma frequencyInterval_mem (j : Fin 7) :
    (frequencyInterval j).Mem (CurrentWindow.frequency j) := by
  unfold frequencyInterval
  split_ifs with hj
  · have hj0 : j = 0 := Fin.ext (by simpa using hj)
    subst j
    exact sqrtTwo_mem
  · rcases j with ⟨_ | n, hn⟩
    · simp at hj
    · convert QInterval.mem_smul pi_mem (2 * (n + 1) : ℚ) using 1 <;>
        simp [CurrentWindow.frequency] <;> ring

lemma minusArgumentInterval_mem {cell : ℕ} (j : Fin 7) {x : ℝ}
    (hx : x ∈ Icc ((cell : ℝ) / 4000) ((cell + 1 : ℕ) / 4000)) :
    (minusArgumentInterval cell j).Mem (minusArgument j x) := by
  have hf := frequencyInterval_mem j
  have hp := piTimesXInterval_mem hx
  have h := QInterval.mem_smul
    (QInterval.mem_sub hf (QInterval.mem_smul hp 2)) (1 / 2)
  convert h using 1 <;> simp [minusArgumentInterval, minusArgument] <;> ring

lemma plusArgumentInterval_mem {cell : ℕ} (j : Fin 7) {x : ℝ}
    (hx : x ∈ Icc ((cell : ℝ) / 4000) ((cell + 1 : ℕ) / 4000)) :
    (plusArgumentInterval cell j).Mem (plusArgument j x) := by
  have hf := frequencyInterval_mem j
  have hp := piTimesXInterval_mem hx
  have h := QInterval.mem_smul
    (QInterval.mem_add hf (QInterval.mem_smul hp 2)) (1 / 2)
  convert h using 1 <;> simp [plusArgumentInterval, plusArgument] <;> ring

/-! ## Ordinary and removable jet rows -/

inductive JetRow where
  | ordinary (row : CheckedSincJet.SignedWitness)
  | nearZero (row : NearZeroTotalSincJet.Witness)

def JetRow.check : JetRow → Bool
  | .ordinary row => row.check
  | .nearZero row => row.check

def JetRow.value : JetRow → QInterval
  | .ordinary row => ⟨row.valueLower, row.valueUpper⟩
  | .nearZero row => ⟨1 - row.valueError, 1 + row.valueError⟩

def JetRow.first : JetRow → QInterval
  | .ordinary row => ⟨row.firstLower, row.firstUpper⟩
  | .nearZero row => ⟨-row.firstError, row.firstError⟩

def JetRow.second' : JetRow → QInterval
  | .ordinary row => ⟨row.secondLower, row.secondUpper⟩
  | .nearZero row => ⟨-(1 / 3) - row.secondError,
      -(1 / 3) + row.secondError⟩

def JetRow.accepts (row : JetRow) (I : QInterval) : Bool :=
  match row with
  | .ordinary row => decide
      (row.center - row.positive.jet.radius ≤ I.lo ∧
        I.hi ≤ row.center + row.positive.jet.radius)
  | .nearZero row => decide (-row.radius ≤ I.lo ∧ I.hi ≤ row.radius)

private lemma interval_abs_center {I : QInterval} {c r : ℚ} {x : ℝ}
    (hinc : c - r ≤ I.lo ∧ I.hi ≤ c + r) (hx : I.Mem x) :
    |x - (c : ℝ)| ≤ (r : ℝ) := by
  rw [abs_le]
  have hincR : (c : ℝ) - r ≤ (I.lo : ℝ) ∧
      (I.hi : ℝ) ≤ (c : ℝ) + r := by exact_mod_cast hinc
  constructor <;> linarith [hx.1, hx.2, hincR.1, hincR.2]

private lemma interval_abs_zero {I : QInterval} {r : ℚ} {x : ℝ}
    (hinc : -r ≤ I.lo ∧ I.hi ≤ r) (hx : I.Mem x) : |x| ≤ (r : ℝ) := by
  rw [abs_le]
  have hincR : -(r : ℝ) ≤ (I.lo : ℝ) ∧ (I.hi : ℝ) ≤ r := by
    exact_mod_cast hinc
  constructor <;> linarith [hx.1, hx.2, hincR.1, hincR.2]

private lemma abs_mem_center {x c e : ℝ} (h : |x - c| ≤ e) :
    c - e ≤ x ∧ x ≤ c + e := by
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

theorem JetRow.sound {row : JetRow} {I : QInterval}
    (hc : row.check = true) (ha : row.accepts I = true) {x : ℝ}
    (hx : I.Mem x) :
    (row.value.Mem (Real.sinc x)) ∧
    (row.first.Mem (sincD1Total x)) ∧
    (row.second'.Mem (sincD2Total x)) := by
  cases row with
  | ordinary row =>
      have hinc : row.center - row.positive.jet.radius ≤ I.lo ∧
          I.hi ≤ row.center + row.positive.jet.radius := by
        simpa [JetRow.accepts] using of_decide_eq_true ha
      have hs := row.sound hc (interval_abs_center hinc hx)
      exact hs
  | nearZero row =>
      have hinc : -row.radius ≤ I.lo ∧ I.hi ≤ row.radius := by
        simpa [JetRow.accepts] using of_decide_eq_true ha
      have hs := row.sound hc (interval_abs_zero hinc hx)
      have hv : (1 : ℝ) - row.valueError ≤ Real.sinc x ∧
          Real.sinc x ≤ 1 + row.valueError := abs_mem_center hs.1
      have hf : -(row.firstError : ℝ) ≤ sincD1Total x ∧
          sincD1Total x ≤ row.firstError := by
        have ht := abs_mem_center (c := (0 : ℝ)) (by simpa using hs.2.1)
        simpa using ht
      have hsecondAbs : |sincD2Total x - (-(1 / 3 : ℝ))| ≤ row.secondError := by
        convert hs.2.2 using 1 <;> ring
      have hsecond := abs_mem_center hsecondAbs
      simpa only [JetRow.value, JetRow.first, JetRow.second',
        QInterval.Mem, Rat.cast_sub, Rat.cast_add, Rat.cast_one,
        Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using ⟨hv, hf, hsecond⟩

/-! ## Rational aggregation -/

def coefficientQ : Fin 7 → ℚ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3322500 / 1000000000
  | ⟨2, _⟩ => -7609135 / 1000000000
  | ⟨3, _⟩ => 1190194 / 1000000000
  | ⟨4, _⟩ => -731476 / 1000000000
  | ⟨5, _⟩ => -1680572 / 1000000000
  | ⟨6, _⟩ => 1141360 / 1000000000

lemma coefficientQ_cast (j : Fin 7) :
    (coefficientQ j : ℝ) = CurrentWindow.coefficient j := by
  fin_cases j <;> norm_num [coefficientQ, CurrentWindow.coefficient]

def piMul (I : QInterval) : QInterval := qmul piInterval I

def kernelInterval (minus plus : Fin 7 → JetRow) : QInterval :=
  qsum fun j => ((minus j).value.add (plus j).value).smul
    (coefficientQ j / 2)

def kernelD1Interval (minus plus : Fin 7 → JetRow) : QInterval :=
  qsum fun j => piMul (((plus j).first.sub (minus j).first).smul
    (coefficientQ j / 2))

def kernelD2Interval (minus plus : Fin 7 → JetRow) : QInterval :=
  qsum fun j => piMul (piMul
    (((minus j).second'.add (plus j).second').smul (coefficientQ j / 2)))

private lemma piInterval_valid : Valid piInterval := by
  norm_num [piInterval, Valid]

private lemma aggregate_kernel_mem {minus plus : Fin 7 → JetRow} {x : ℝ}
    (hm : ∀ j, (minus j).value.Mem (Real.sinc (minusArgument j x)))
    (hp : ∀ j, (plus j).value.Mem (Real.sinc (plusArgument j x))) :
    (kernelInterval minus plus).Mem (CurrentKernelFormula.closedKernel x) := by
  unfold kernelInterval CurrentKernelFormula.closedKernel
  apply QInterval.mem_sum
  intro j
  have h := QInterval.mem_smul (QInterval.mem_add (hm j) (hp j))
    (coefficientQ j / 2)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  rw [coefficientQ_cast] at h
  convert h using 1 <;> simp [minusArgument, plusArgument] <;> ring

private lemma aggregate_kernelD1_mem {minus plus : Fin 7 → JetRow} {x : ℝ}
    (hm : ∀ j, (minus j).first.Mem (sincD1Total (minusArgument j x)))
    (hp : ∀ j, (plus j).first.Mem (sincD1Total (plusArgument j x)))
    (hv : ∀ j, Valid ((plus j).first.sub (minus j).first)) :
    (kernelD1Interval minus plus).Mem (closedKernelD1Total x) := by
  unfold kernelD1Interval closedKernelD1Total piMul
  apply QInterval.mem_sum
  intro j
  have hd := QInterval.mem_sub (hp j) (hm j)
  have hs := QInterval.mem_smul hd (coefficientQ j / 2)
  have hvalid := QInterval.valid_smul (hv j) (coefficientQ j / 2)
  have hpi := QInterval.mem_mul piInterval_valid hvalid pi_mem hs
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hpi
  rw [coefficientQ_cast] at hpi
  convert hpi using 1 <;> ring

private lemma aggregate_kernelD2_mem {minus plus : Fin 7 → JetRow} {x : ℝ}
    (hm : ∀ j, (minus j).second'.Mem (sincD2Total (minusArgument j x)))
    (hp : ∀ j, (plus j).second'.Mem (sincD2Total (plusArgument j x)))
    (hv : ∀ j, Valid ((minus j).second'.add (plus j).second')) :
    (kernelD2Interval minus plus).Mem (closedKernelD2Total x) := by
  unfold kernelD2Interval closedKernelD2Total piMul
  apply QInterval.mem_sum
  intro j
  have ha := QInterval.mem_add (hm j) (hp j)
  have hs := QInterval.mem_smul ha (coefficientQ j / 2)
  have hvalid := QInterval.valid_smul (hv j) (coefficientQ j / 2)
  have hp1 := QInterval.mem_mul piInterval_valid hvalid pi_mem hs
  have hv1 := QInterval.valid_mul piInterval_valid hvalid
  have hp2 := QInterval.mem_mul piInterval_valid hv1 pi_mem hp1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hp2
  rw [coefficientQ_cast] at hp2
  convert hp2 using 1 <;> simp [pow_two] <;> ring

/-! ## Sign-general normalized weight arithmetic -/

def k0Interval : QInterval := ⟨918707 / 1000000, 918744 / 1000000⟩
def invK0SqInterval : QInterval :=
  ⟨1 / (k0Interval.hi ^ 2), 1 / (k0Interval.lo ^ 2)⟩

private lemma closedKernel_zero_eq_sinc :
    CurrentKernelFormula.closedKernel 0 = Real.sinc (Real.sqrt 2 / 2) := by
  rw [CurrentWindowClosedHAssembly.closedKernel_zero_eq,
    Real.sinc_of_ne_zero (div_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
      (by norm_num))]
  ring

private lemma k0Interval_mem : k0Interval.Mem (CurrentKernelFormula.closedKernel 0) := by
  rw [closedKernel_zero_eq_sinc]
  simpa [k0Interval, QInterval.Mem] using
    CurrentKernelDerivatives.sinc_sqrt_two_half_bounds

private lemma invK0SqInterval_mem :
    invK0SqInterval.Mem (1 / CurrentKernelFormula.closedKernel 0 ^ 2) := by
  have hk := k0Interval_mem
  have hlo : (0 : ℝ) < k0Interval.lo := by norm_num [k0Interval]
  have hkpos : 0 < CurrentKernelFormula.closedKernel 0 := hlo.trans_le hk.1
  have hhi : (0 : ℝ) < k0Interval.hi := hlo.trans_le (by
    norm_num [k0Interval])
  constructor
  · change (1 / (k0Interval.hi ^ 2) : ℚ) ≤
      (1 / CurrentKernelFormula.closedKernel 0 ^ 2 : ℝ)
    push_cast
    rw [div_le_div_iff₀ (sq_pos_of_pos hhi) (sq_pos_of_pos hkpos)]
    nlinarith [hk.2]
  · change (1 / CurrentKernelFormula.closedKernel 0 ^ 2 : ℝ) ≤
      (1 / (k0Interval.lo ^ 2) : ℚ)
    push_cast
    rw [div_le_div_iff₀ (sq_pos_of_pos hkpos) (sq_pos_of_pos hlo)]
    nlinarith [hk.1]

def numeratorInterval (minus plus : Fin 7 → JetRow) : QInterval :=
  let K := kernelInterval minus plus
  let K1 := kernelD1Interval minus plus
  let K2 := kernelD2Interval minus plus
  ((qmul K1 K1).add (qmul K K2)).smul 2

def weightD2Interval (minus plus : Fin 7 → JetRow) : QInterval :=
  qmul (numeratorInterval minus plus) invK0SqInterval

/-- Complete generated data for one grid cell. -/
structure CellWitness where
  cell : ℕ
  minus : Fin 7 → JetRow
  plus : Fin 7 → JetRow
  lower : ℚ

noncomputable def CellWitness.check (w : CellWitness) : Bool := by
  classical
  exact decide (
    (∀ j, (w.minus j).check = true ∧
      (w.minus j).accepts (minusArgumentInterval w.cell j) = true ∧
      Valid (w.minus j).value ∧ Valid (w.minus j).first ∧
      Valid (w.minus j).second') ∧
    (∀ j, (w.plus j).check = true ∧
      (w.plus j).accepts (plusArgumentInterval w.cell j) = true ∧
      Valid (w.plus j).value ∧ Valid (w.plus j).first ∧
      Valid (w.plus j).second') ∧
    w.lower ≤ (weightD2Interval w.minus w.plus).lo)

private lemma cell_check_facts {w : CellWitness} (h : w.check = true) :
    (∀ j, (w.minus j).check = true ∧
      (w.minus j).accepts (minusArgumentInterval w.cell j) = true ∧
      Valid (w.minus j).value ∧ Valid (w.minus j).first ∧
      Valid (w.minus j).second') ∧
    (∀ j, (w.plus j).check = true ∧
      (w.plus j).accepts (plusArgumentInterval w.cell j) = true ∧
      Valid (w.plus j).value ∧ Valid (w.plus j).first ∧
      Valid (w.plus j).second') ∧
    w.lower ≤ (weightD2Interval w.minus w.plus).lo := by
  simpa [CellWitness.check] using of_decide_eq_true h

/-- Soundness of a fully checked current `w''` table cell, with no sign
assumptions and with removable arguments handled by total jets. -/
theorem CellWitness.sound (w : CellWitness) (h : w.check = true) {x : ℝ}
    (hx : x ∈ Icc ((w.cell : ℝ) / 4000) ((w.cell + 1 : ℕ) / 4000)) :
    (w.lower : ℝ) ≤ closedWeightD2Total x := by
  have hf := cell_check_facts h
  have hm (j : Fin 7) := JetRow.sound (hf.1 j).1 (hf.1 j).2.1
    (minusArgumentInterval_mem j hx)
  have hp (j : Fin 7) := JetRow.sound (hf.2.1 j).1 (hf.2.1 j).2.1
    (plusArgumentInterval_mem j hx)
  have hK := aggregate_kernel_mem (fun j => (hm j).1) (fun j => (hp j).1)
  have hK1 := aggregate_kernelD1_mem (fun j => (hm j).2.1) (fun j => (hp j).2.1)
    (fun j => QInterval.valid_sub (hf.2.1 j).2.2.2.1
      (hf.1 j).2.2.2.1)
  have hK2 := aggregate_kernelD2_mem (fun j => (hm j).2.2) (fun j => (hp j).2.2)
    (fun j => QInterval.valid_add (hf.1 j).2.2.2.2
      (hf.2.1 j).2.2.2.2)
  have vK := QInterval.valid_sum fun j => QInterval.valid_smul
    (QInterval.valid_add (hf.1 j).2.2.1 (hf.2.1 j).2.2.1)
      (coefficientQ j / 2)
  have vK1 := QInterval.valid_sum fun j => QInterval.valid_mul piInterval_valid
    (QInterval.valid_smul
      (QInterval.valid_sub (hf.2.1 j).2.2.2.1 (hf.1 j).2.2.2.1)
      (coefficientQ j / 2))
  have vK2 := QInterval.valid_sum fun j => QInterval.valid_mul piInterval_valid
    (QInterval.valid_mul piInterval_valid (QInterval.valid_smul
      (QInterval.valid_add (hf.1 j).2.2.2.2 (hf.2.1 j).2.2.2.2)
      (coefficientQ j / 2)))
  have hnum : (numeratorInterval w.minus w.plus).Mem
      (2 * (closedKernelD1Total x ^ 2 +
        CurrentKernelFormula.closedKernel x * closedKernelD2Total x)) := by
    unfold numeratorInterval
    have ht := QInterval.mem_smul
      (QInterval.mem_add (QInterval.mem_mul vK1 vK1 hK1 hK1)
        (QInterval.mem_mul vK vK2 hK hK2)) 2
    norm_num only [Nat.cast_ofNat] at ht
    simpa only [kernelInterval, kernelD1Interval, kernelD2Interval,
      piMul, pow_two] using ht
  have vnum : Valid (numeratorInterval w.minus w.plus) := by
    unfold numeratorInterval
    exact QInterval.valid_smul
      (QInterval.valid_add (QInterval.valid_mul vK1 vK1)
        (QInterval.valid_mul vK vK2)) 2
  have vinv : Valid invK0SqInterval := by
    norm_num [invK0SqInterval, k0Interval, Valid]
  have hw := QInterval.mem_mul vnum vinv hnum invK0SqInterval_mem
  have hlower : (w.lower : ℝ) ≤
      (weightD2Interval w.minus w.plus).lo := by exact_mod_cast hf.2.2
  exact hlower.trans (by
    simpa [weightD2Interval, closedWeightD2Total, div_eq_mul_inv] using hw.1)

/-! ## Value and first-derivative projections

The tangent-center checker uses the same fourteen jets.  These interval
projections avoid replaying any transcendental work for `w` and `w'`. -/

def weightInterval (minus plus : Fin 7 → JetRow) : QInterval :=
  qmul (qmul (kernelInterval minus plus) (kernelInterval minus plus))
    invK0SqInterval

def weightD1Interval (minus plus : Fin 7 → JetRow) : QInterval :=
  (qmul (qmul (kernelInterval minus plus) (kernelD1Interval minus plus))
    invK0SqInterval).smul 2

theorem CellWitness.value_first_sound (w : CellWitness) (h : w.check = true) {x : ℝ}
    (hx : x ∈ Icc ((w.cell : ℝ) / 4000) ((w.cell + 1 : ℕ) / 4000)) :
    (weightInterval w.minus w.plus).Mem (CurrentWindow.weight x) ∧
    (weightD1Interval w.minus w.plus).Mem (closedWeightD1Total x) := by
  have hf := cell_check_facts h
  have hm (j : Fin 7) := JetRow.sound (hf.1 j).1 (hf.1 j).2.1
    (minusArgumentInterval_mem j hx)
  have hp (j : Fin 7) := JetRow.sound (hf.2.1 j).1 (hf.2.1 j).2.1
    (plusArgumentInterval_mem j hx)
  have hK := aggregate_kernel_mem (fun j => (hm j).1) (fun j => (hp j).1)
  have hK1 := aggregate_kernelD1_mem (fun j => (hm j).2.1) (fun j => (hp j).2.1)
    (fun j => QInterval.valid_sub (hf.2.1 j).2.2.2.1
      (hf.1 j).2.2.2.1)
  have vK := QInterval.valid_sum fun j => QInterval.valid_smul
    (QInterval.valid_add (hf.1 j).2.2.1 (hf.2.1 j).2.2.1)
      (coefficientQ j / 2)
  have vK1 := QInterval.valid_sum fun j => QInterval.valid_mul piInterval_valid
    (QInterval.valid_smul
      (QInterval.valid_sub (hf.2.1 j).2.2.2.1 (hf.1 j).2.2.2.1)
      (coefficientQ j / 2))
  have vinv : Valid invK0SqInterval := by
    norm_num [invK0SqInterval, k0Interval, Valid]
  constructor
  · have hsquare := QInterval.mem_mul vK vK hK hK
    have hsound := QInterval.mem_mul (QInterval.valid_mul vK vK) vinv
      hsquare invK0SqInterval_mem
    rw [CurrentKernelFormula.weight_eq_closedKernel]
    simpa [weightInterval, kernelInterval, div_pow, div_eq_mul_inv, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using hsound
  · have hprod := QInterval.mem_mul vK vK1 hK hK1
    have hscaled := QInterval.mem_mul (QInterval.valid_mul vK vK1) vinv
      hprod invK0SqInterval_mem
    have htwo := QInterval.mem_smul hscaled 2
    norm_num only [Nat.cast_ofNat] at htwo
    simpa [weightD1Interval, kernelInterval, kernelD1Interval, piMul,
      closedWeightD1Total, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using htwo

end Zeta23Ext.CurrentWeightD2CellChecker
end
