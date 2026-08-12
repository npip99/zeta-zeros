/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentKernelFormula
import Zeta23Ext.SincDerivativeCertificate

/-!
# Derivatives and error combination for the current closed kernel

This file connects the verifier's termwise sinc-jet rows to exact derivatives
of its seven-term kernel.  It deliberately keeps generated table data out of
the semantic theorem: a producer supplies fourteen absolute-error rows, and
the theorem combines them with the exact coefficient signs.
-/

noncomputable section

open Real Set Filter Topology
open scoped BigOperators

namespace Zeta23Ext.CurrentKernelDerivatives

open CurrentWindow
open CurrentKernelFormula
open SincDerivativeCertificate

def minusArgument (j : Fin 7) (x : ℝ) : ℝ :=
  (frequency j - 2 * Real.pi * x) / 2

def plusArgument (j : Fin 7) (x : ℝ) : ℝ :=
  (frequency j + 2 * Real.pi * x) / 2

/-- The exact first derivative expression used by the interval producer. -/
def closedKernelD1 (x : ℝ) : ℝ :=
  ∑ j : Fin 7, coefficient j * Real.pi *
    (sincD1 (plusArgument j x) - sincD1 (minusArgument j x)) / 2

/-- The exact second derivative expression used by the interval producer. -/
def closedKernelD2 (x : ℝ) : ℝ :=
  ∑ j : Fin 7, coefficient j * Real.pi ^ 2 *
    (sincD2 (minusArgument j x) + sincD2 (plusArgument j x)) / 2

lemma hasDerivAt_minusArgument (j : Fin 7) (x : ℝ) :
    HasDerivAt (minusArgument j) (-Real.pi) x := by
  unfold minusArgument
  have h := ((hasDerivAt_const x (frequency j)).sub
    ((hasDerivAt_id x).const_mul (2 * Real.pi))).div_const 2
  apply h.congr_deriv
  ring

lemma hasDerivAt_plusArgument (j : Fin 7) (x : ℝ) :
    HasDerivAt (plusArgument j) Real.pi x := by
  unfold plusArgument
  have h := ((hasDerivAt_const x (frequency j)).add
    ((hasDerivAt_id x).const_mul (2 * Real.pi))).div_const 2
  apply h.congr_deriv
  ring

/-- `closedKernelD1` really is the derivative of the exact closed kernel at
every point where none of the fourteen closed-form sinc arguments vanishes. -/
theorem hasDerivAt_closedKernel (x : ℝ)
    (hneMinus : ∀ j : Fin 7, minusArgument j x ≠ 0)
    (hnePlus : ∀ j : Fin 7, plusArgument j x ≠ 0) :
    HasDerivAt closedKernel (closedKernelD1 x) x := by
  unfold closedKernel closedKernelD1
  apply HasDerivAt.fun_sum
  intro j _
  have hm := (hasDerivAt_sinc (hneMinus j)).comp x
    (hasDerivAt_minusArgument j x)
  have hp := (hasDerivAt_sinc (hnePlus j)).comp x
    (hasDerivAt_plusArgument j x)
  have h := ((hm.add hp).div_const 2).const_mul (coefficient j)
  have hd : coefficient j *
      ((sincD1 (minusArgument j x) * -Real.pi +
        sincD1 (plusArgument j x) * Real.pi) / 2) =
      coefficient j * Real.pi *
        (sincD1 (plusArgument j x) - sincD1 (minusArgument j x)) / 2 := by
    ring
  have h' := h.congr_deriv hd
  apply h'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by
    simp only [Function.comp_apply, Pi.add_apply, minusArgument, plusArgument]
    ring

/-- `closedKernelD2` really is the derivative of `closedKernelD1` under the
same away-from-zero condition. -/
theorem hasDerivAt_closedKernelD1 (x : ℝ)
    (hneMinus : ∀ j : Fin 7, minusArgument j x ≠ 0)
    (hnePlus : ∀ j : Fin 7, plusArgument j x ≠ 0) :
    HasDerivAt closedKernelD1 (closedKernelD2 x) x := by
  unfold closedKernelD1 closedKernelD2
  apply HasDerivAt.fun_sum
  intro j _
  have hm := (hasDerivAt_sincD1 (hneMinus j)).comp x
    (hasDerivAt_minusArgument j x)
  have hp := (hasDerivAt_sincD1 (hnePlus j)).comp x
    (hasDerivAt_plusArgument j x)
  have h := ((hp.sub hm).const_mul (coefficient j * Real.pi)).div_const 2
  simpa only [Function.comp_apply, Pi.sub_apply] using
    (h.congr_deriv (by ring))

/-- Exact expression for the second derivative of the squared normalized
kernel.  The normalization is kept explicit because its rational enclosure
is a separate one-row witness. -/
def closedWeightD2 (x : ℝ) : ℝ :=
  2 * (closedKernelD1 x ^ 2 + closedKernel x * closedKernelD2 x) /
    closedKernel 0 ^ 2

theorem hasDerivAt_closedWeightD1 (x : ℝ)
    (hneMinus : ∀ j : Fin 7, minusArgument j x ≠ 0)
    (hnePlus : ∀ j : Fin 7, plusArgument j x ≠ 0) :
    HasDerivAt
      (fun y => 2 * closedKernel y * closedKernelD1 y / closedKernel 0 ^ 2)
      (closedWeightD2 x) x := by
  have hk := hasDerivAt_closedKernel x hneMinus hnePlus
  have hk1 := hasDerivAt_closedKernelD1 x hneMinus hnePlus
  have h := (((hk.const_mul 2).mul hk1).div_const (closedKernel 0 ^ 2))
  apply h.congr_deriv
  unfold closedWeightD2
  ring

/-! ## Absolute-error rows and their seven-term combination -/

/-- Absolute-error data for the two sinc arguments of one frequency. -/
structure PairApprox where
  minusValue : ℝ
  plusValue : ℝ
  minusFirst : ℝ
  plusFirst : ℝ
  minusSecond : ℝ
  plusSecond : ℝ
  minusValueError : ℝ
  plusValueError : ℝ
  minusFirstError : ℝ
  plusFirstError : ℝ
  minusSecondError : ℝ
  plusSecondError : ℝ

def approximateKernel (row : Fin 7 → PairApprox) : ℝ :=
  ∑ j, (coefficient j * (row j).minusValue +
    coefficient j * (row j).plusValue) / 2

def approximateKernelD1 (row : Fin 7 → PairApprox) : ℝ :=
  ∑ j, coefficient j * Real.pi *
    ((row j).plusFirst - (row j).minusFirst) / 2

def approximateKernelD2 (row : Fin 7 → PairApprox) : ℝ :=
  ∑ j, coefficient j * Real.pi ^ 2 *
    ((row j).minusSecond + (row j).plusSecond) / 2

def kernelError (row : Fin 7 → PairApprox) : ℝ :=
  ∑ j, |coefficient j| *
    ((row j).minusValueError + (row j).plusValueError) / 2

def kernelD1Error (row : Fin 7 → PairApprox) : ℝ :=
  ∑ j, |coefficient j * Real.pi| *
    ((row j).minusFirstError + (row j).plusFirstError) / 2

def kernelD2Error (row : Fin 7 → PairApprox) : ℝ :=
  ∑ j, |coefficient j * Real.pi ^ 2| *
    ((row j).minusSecondError + (row j).plusSecondError) / 2

private theorem abs_pair_sum_le {n : ℕ}
    (c actualLeft actualRight approxLeft approxRight errorLeft errorRight : Fin n → ℝ)
    (hl : ∀ j, |actualLeft j - approxLeft j| ≤ errorLeft j)
    (hr : ∀ j, |actualRight j - approxRight j| ≤ errorRight j) :
    |∑ j, c j * (actualLeft j + actualRight j) / 2 -
      ∑ j, c j * (approxLeft j + approxRight j) / 2| ≤
      ∑ j, |c j| * (errorLeft j + errorRight j) / 2 := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j, (c j * (actualLeft j + actualRight j) / 2 -
        c j * (approxLeft j + approxRight j) / 2)| ≤
        ∑ j, |c j * (actualLeft j + actualRight j) / 2 -
          c j * (approxLeft j + approxRight j) / 2| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |c j| * (errorLeft j + errorRight j) / 2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [show c j * (actualLeft j + actualRight j) / 2 -
          c j * (approxLeft j + approxRight j) / 2 =
          c j / 2 * ((actualLeft j - approxLeft j) +
            (actualRight j - approxRight j)) by ring,
        abs_mul, abs_div]
      norm_num
      calc
        |c j| / 2 * |(actualLeft j - approxLeft j) +
            (actualRight j - approxRight j)| ≤
            |c j| / 2 * (|actualLeft j - approxLeft j| +
              |actualRight j - approxRight j|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _)
            (div_nonneg (abs_nonneg _) (by norm_num))
        _ ≤ |c j| / 2 * (errorLeft j + errorRight j) :=
          mul_le_mul_of_nonneg_left (add_le_add (hl j) (hr j))
            (div_nonneg (abs_nonneg _) (by norm_num))
        _ = |c j| * (errorLeft j + errorRight j) / 2 := by ring

/-- Fourteen sinc-value errors combine into an error for `K`. -/
theorem abs_closedKernel_sub_approximateKernel_le (x : ℝ)
    (row : Fin 7 → PairApprox)
    (hm : ∀ j, |Real.sinc (minusArgument j x) - (row j).minusValue| ≤
      (row j).minusValueError)
    (hp : ∀ j, |Real.sinc (plusArgument j x) - (row j).plusValue| ≤
      (row j).plusValueError) :
    |closedKernel x - approximateKernel row| ≤ kernelError row := by
  unfold closedKernel approximateKernel kernelError
  simp only [minusArgument, plusArgument] at hm hp
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j : Fin 7, (coefficient j *
          (Real.sinc ((frequency j - 2 * Real.pi * x) / 2) +
            Real.sinc ((frequency j + 2 * Real.pi * x) / 2)) / 2 -
        (coefficient j * (row j).minusValue +
          coefficient j * (row j).plusValue) / 2)| ≤
        ∑ j : Fin 7, |coefficient j| *
          ((row j).minusValueError + (row j).plusValueError) / 2 := by
      calc
        |∑ j : Fin 7, (coefficient j *
            (Real.sinc ((frequency j - 2 * Real.pi * x) / 2) +
              Real.sinc ((frequency j + 2 * Real.pi * x) / 2)) / 2 -
            (coefficient j * (row j).minusValue +
              coefficient j * (row j).plusValue) / 2)| ≤
            ∑ j : Fin 7, |coefficient j *
              (Real.sinc ((frequency j - 2 * Real.pi * x) / 2) +
                Real.sinc ((frequency j + 2 * Real.pi * x) / 2)) / 2 -
              (coefficient j * (row j).minusValue +
                coefficient j * (row j).plusValue) / 2| :=
                  Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin 7, |coefficient j| *
            ((row j).minusValueError + (row j).plusValueError) / 2 := by
          apply Finset.sum_le_sum
          intro j _
          rw [show coefficient j *
          (Real.sinc ((frequency j - 2 * Real.pi * x) / 2) +
            Real.sinc ((frequency j + 2 * Real.pi * x) / 2)) / 2 -
          (coefficient j * (row j).minusValue +
            coefficient j * (row j).plusValue) / 2 =
          coefficient j / 2 *
            ((Real.sinc ((frequency j - 2 * Real.pi * x) / 2) -
              (row j).minusValue) +
             (Real.sinc ((frequency j + 2 * Real.pi * x) / 2) -
              (row j).plusValue)) by ring]
          rw [abs_mul, abs_div]
          norm_num
          calc
            |coefficient j| / 2 *
            |(Real.sinc ((frequency j - 2 * Real.pi * x) / 2) -
                (row j).minusValue) +
              (Real.sinc ((frequency j + 2 * Real.pi * x) / 2) -
                (row j).plusValue)| ≤
            |coefficient j| / 2 *
              (|(Real.sinc ((frequency j - 2 * Real.pi * x) / 2) -
                  (row j).minusValue)| +
                |(Real.sinc ((frequency j + 2 * Real.pi * x) / 2) -
                  (row j).plusValue)|) := by
                gcongr
                exact abs_add_le _ _
            _ ≤ |coefficient j| / 2 *
                ((row j).minusValueError + (row j).plusValueError) :=
              mul_le_mul_of_nonneg_left (add_le_add (hm j) (hp j))
                (div_nonneg (abs_nonneg _) (by norm_num))
            _ = |coefficient j| *
                ((row j).minusValueError + (row j).plusValueError) / 2 := by ring
    _ = ∑ j : Fin 7, |coefficient j| *
        ((row j).minusValueError + (row j).plusValueError) / 2 := rfl

/-- Fourteen first-derivative rows combine with the exact `π/2` chain-rule
factor and the subtraction sign on the minus argument. -/
theorem abs_closedKernelD1_sub_approximateKernelD1_le (x : ℝ)
    (row : Fin 7 → PairApprox)
    (hm : ∀ j, |sincD1 (minusArgument j x) - (row j).minusFirst| ≤
      (row j).minusFirstError)
    (hp : ∀ j, |sincD1 (plusArgument j x) - (row j).plusFirst| ≤
      (row j).plusFirstError) :
    |closedKernelD1 x - approximateKernelD1 row| ≤ kernelD1Error row := by
  unfold closedKernelD1 approximateKernelD1 kernelD1Error
  have h := abs_pair_sum_le
    (c := fun j : Fin 7 => coefficient j * Real.pi)
    (actualLeft := fun j => sincD1 (plusArgument j x))
    (actualRight := fun j => -sincD1 (minusArgument j x))
    (approxLeft := fun j => (row j).plusFirst)
    (approxRight := fun j => -(row j).minusFirst)
    (errorLeft := fun j => (row j).plusFirstError)
    (errorRight := fun j => (row j).minusFirstError)
    hp (fun j => by simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using hm j)
  simpa only [sub_eq_add_neg, add_comm] using h

/-- Fourteen second-derivative rows combine with the exact `π²/2`
chain-rule factor. -/
theorem abs_closedKernelD2_sub_approximateKernelD2_le (x : ℝ)
    (row : Fin 7 → PairApprox)
    (hm : ∀ j, |sincD2 (minusArgument j x) - (row j).minusSecond| ≤
      (row j).minusSecondError)
    (hp : ∀ j, |sincD2 (plusArgument j x) - (row j).plusSecond| ≤
      (row j).plusSecondError) :
    |closedKernelD2 x - approximateKernelD2 row| ≤ kernelD2Error row := by
  unfold closedKernelD2 approximateKernelD2 kernelD2Error
  exact abs_pair_sum_le
    (c := fun j : Fin 7 => coefficient j * Real.pi ^ 2)
    (actualLeft := fun j => sincD2 (minusArgument j x))
    (actualRight := fun j => sincD2 (plusArgument j x))
    (approxLeft := fun j => (row j).minusSecond)
    (approxRight := fun j => (row j).plusSecond)
    (errorLeft := fun j => (row j).minusSecondError)
    (errorRight := fun j => (row j).plusSecondError) hm hp

/-! ## Sign-aware final interval arithmetic -/

/-- The sign pattern occurring at production cell 4376: `K` and `K'` are
negative, while `K''` and `K(0)` are positive.  Under that pattern this lemma
reduces a lower bound for `w''` to one scalar rational inequality. -/
theorem closedWeightD2_lower_of_sign_bounds {x lower kLower k1Upper k2Upper k0Upper : ℝ}
    (hlower : 0 ≤ lower)
    (hkLower : kLower ≤ closedKernel x)
    (hkNonpos : closedKernel x ≤ 0)
    (hk1Upper : closedKernelD1 x ≤ k1Upper)
    (hk1Nonpos : k1Upper ≤ 0)
    (hk2Nonneg : 0 ≤ closedKernelD2 x)
    (hk2Upper : closedKernelD2 x ≤ k2Upper)
    (hk0Pos : 0 < closedKernel 0)
    (hk0Upper : closedKernel 0 ≤ k0Upper)
    (harithmetic : lower * k0Upper ^ 2 ≤
      2 * (k1Upper ^ 2 + kLower * k2Upper)) :
    lower ≤ closedWeightD2 x := by
  have hkLowerNonpos : kLower ≤ 0 := hkLower.trans hkNonpos
  have hk2UpperNonneg : 0 ≤ k2Upper := hk2Nonneg.trans hk2Upper
  have hk1Sq : k1Upper ^ 2 ≤ closedKernelD1 x ^ 2 := by
    nlinarith
  have hkProduct : kLower * k2Upper ≤
      closedKernel x * closedKernelD2 x := by
    calc
      kLower * k2Upper ≤ kLower * closedKernelD2 x :=
        mul_le_mul_of_nonpos_left hk2Upper hkLowerNonpos
      _ ≤ closedKernel x * closedKernelD2 x :=
        mul_le_mul_of_nonneg_right hkLower hk2Nonneg
  have hnum : lower * k0Upper ^ 2 ≤
      2 * (closedKernelD1 x ^ 2 + closedKernel x * closedKernelD2 x) := by
    calc
      lower * k0Upper ^ 2 ≤
          2 * (k1Upper ^ 2 + kLower * k2Upper) := harithmetic
      _ ≤ 2 * (closedKernelD1 x ^ 2 +
          closedKernel x * closedKernelD2 x) := by gcongr
  have hk0UpperNonneg : 0 ≤ k0Upper := hk0Pos.le.trans hk0Upper
  have hden : closedKernel 0 ^ 2 ≤ k0Upper ^ 2 := by gcongr
  have hscaled : lower * closedKernel 0 ^ 2 ≤
      2 * (closedKernelD1 x ^ 2 + closedKernel x * closedKernelD2 x) :=
    (mul_le_mul_of_nonneg_left hden hlower).trans hnum
  unfold closedWeightD2
  rw [le_div_iff₀ (sq_pos_of_pos hk0Pos)]
  exact hscaled

/-! ## Production cell 4376 arithmetic regression -/

/-- The exact rational represented by the downward-rounded binary64 table
entry at index 4376. -/
def cell4376Lower : ℚ := 5318105815318527 / 4503599627370496

/-- The final scalar comparison for cell 4376 has substantial room after the
four aggregate enclosures are rounded outwards to six decimals.  Supplying
those aggregate enclosures from fourteen checked sinc-jet rows is now the
only semantic premise remaining for this representative cell. -/
theorem cell4376_scalar_check :
    (cell4376Lower : ℝ) * ((918744 : ℝ) / 1000000) ^ 2 ≤
      2 * (((-741272 : ℝ) / 1000000) ^ 2 +
        ((-27161 : ℝ) / 1000000) * ((1868189 : ℝ) / 1000000)) := by
  norm_num [cell4376Lower]

/-- No removable sinc point occurs anywhere in production cell 4376. -/
theorem cell4376_arguments_nonzero {x : ℝ}
    (hx : x ∈ Set.Icc ((4376 : ℝ) / 4000) (4377 / 4000)) :
    (∀ j : Fin 7, minusArgument j x ≠ 0) ∧
      (∀ j : Fin 7, plusArgument j x ≠ 0) := by
  have hxOne : 1 < x := by norm_num at hx ⊢; linarith [hx.1]
  have hxTwo : x < 2 := by norm_num at hx ⊢; linarith [hx.2]
  have hxPos : 0 < x := lt_trans zero_lt_one hxOne
  have hpi := Real.pi_gt_three
  have hsqrtUpper : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  constructor
  · intro j
    fin_cases j
    · simp only [minusArgument, frequency]
      apply div_ne_zero
      · intro hzero
        have hlarge : Real.sqrt 2 < 2 * Real.pi * x := by
          have : 2 < 2 * Real.pi * x := by nlinarith [mul_pos Real.pi_pos hxPos]
          exact hsqrtUpper.trans this
        nlinarith
      · norm_num
    · simp only [minusArgument, frequency]
      apply div_ne_zero
      · have hfac : 2 * Real.pi * (1 - x) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
            (sub_ne_zero.mpr hxOne.ne)
        convert hfac using 1
        norm_num
        ring
      · norm_num
    · simp only [minusArgument, frequency]
      apply div_ne_zero
      · have hfac : 2 * Real.pi * (2 - x) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
            (sub_ne_zero.mpr hxTwo.ne')
        convert hfac using 1
        norm_num
        ring
      · norm_num
    · simp only [minusArgument, frequency]
      apply div_ne_zero
      · have hfac : 2 * Real.pi * (3 - x) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
            (sub_ne_zero.mpr (by nlinarith [hxTwo]))
        convert hfac using 1
        norm_num
        ring
      · norm_num
    · simp only [minusArgument, frequency]
      apply div_ne_zero
      · have hfac : 2 * Real.pi * (4 - x) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
            (sub_ne_zero.mpr (by nlinarith [hxTwo]))
        convert hfac using 1
        norm_num
        ring
      · norm_num
    · simp only [minusArgument, frequency]
      apply div_ne_zero
      · have hfac : 2 * Real.pi * (5 - x) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
            (sub_ne_zero.mpr (by nlinarith [hxTwo]))
        convert hfac using 1
        norm_num
        ring
      · norm_num
    · simp only [minusArgument, frequency]
      apply div_ne_zero
      · have hfac : 2 * Real.pi * (6 - x) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
            (sub_ne_zero.mpr (by nlinarith [hxTwo]))
        convert hfac using 1
        norm_num
        ring
      · norm_num
  · intro j
    fin_cases j <;> simp only [plusArgument, frequency] <;>
      norm_num <;> positivity

end Zeta23Ext.CurrentKernelDerivatives

end
