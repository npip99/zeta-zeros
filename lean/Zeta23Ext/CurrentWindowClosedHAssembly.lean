/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowClosedHMixed

/-! # Assembly of the current strict `H` certificate -/

noncomputable section

open Real
open scoped BigOperators

namespace Zeta23Ext.CurrentWindowClosedHAssembly

open CurrentWindow
open CurrentWindowFiniteCertificate
open CurrentWindowClosedHScalable
open CurrentWindowClosedHMixed

def periodicCorrection : ℝ :=
  (3322500 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (4 * Real.pi ^ 2)) +
  (-7609135 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (16 * Real.pi ^ 2)) +
  (1190194 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (36 * Real.pi ^ 2)) +
  (-731476 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (64 * Real.pi ^ 2)) +
  (-1680572 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (100 * Real.pi ^ 2)) +
  (1141360 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (144 * Real.pi ^ 2))

private lemma sinc_pi_mul_eq_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sinc (Real.pi * k) = 0 := by
  rw [show Real.pi * (k : ℝ) = (k : ℝ) * Real.pi by ring,
    Real.sinc_of_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hk) Real.pi_ne_zero),
    Real.sin_nat_mul_pi]
  norm_num

private def periodicDiagonal (k : Fin 6) : ℝ :=
  match k.1 with
  | 0 => (3322500 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (4 * Real.pi ^ 2))
  | 1 => (-7609135 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (16 * Real.pi ^ 2))
  | 2 => (1190194 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (36 * Real.pi ^ 2))
  | 3 => (-731476 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (64 * Real.pi ^ 2))
  | 4 => (-1680572 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (100 * Real.pi ^ 2))
  | _ => (1141360 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (144 * Real.pi ^ 2))

private theorem combinedEntry_periodic_local (k l : Fin 6) :
    combinedEntry k.succ l.succ = if k = l then periodicDiagonal k else 0 := by
  have z1 := sinc_pi_mul_eq_zero 1 (by norm_num)
  have z2 := sinc_pi_mul_eq_zero 2 (by norm_num)
  have z3 := sinc_pi_mul_eq_zero 3 (by norm_num)
  have z4 := sinc_pi_mul_eq_zero 4 (by norm_num)
  have z5 := sinc_pi_mul_eq_zero 5 (by norm_num)
  have z6 := sinc_pi_mul_eq_zero 6 (by norm_num)
  have z7 := sinc_pi_mul_eq_zero 7 (by norm_num)
  have z8 := sinc_pi_mul_eq_zero 8 (by norm_num)
  have z9 := sinc_pi_mul_eq_zero 9 (by norm_num)
  have z10 := sinc_pi_mul_eq_zero 10 (by norm_num)
  have z11 := sinc_pi_mul_eq_zero 11 (by norm_num)
  have z12 := sinc_pi_mul_eq_zero 12 (by norm_num)
  norm_num at z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12
  ring_nf at z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12
  fin_cases k <;> fin_cases l <;>
    unfold combinedEntry periodicDiagonal absKernelIntegral cosCosIntegral <;>
    norm_num [coefficient, frequency] <;>
    ring_nf <;>
    simp only [Real.sinc_neg, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10,
      z11, z12] <;>
    field_simp [Real.pi_ne_zero] <;> ring

theorem periodic_block_eq_correction :
    (∑ k : Fin 6, ∑ l : Fin 6, combinedEntry k.succ l.succ) =
      periodicCorrection := by
  simp_rw [combinedEntry_periodic_local]
  simp
  unfold periodicDiagonal
  norm_num [Fin.sum_univ_succ, periodicCorrection]
  ring

private theorem entry_sum_decomposition :
    (∑ i : Fin 7, ∑ j : Fin 7, combinedEntry i j) =
      combinedEntry 0 0 +
        ∑ k : Fin 6, (combinedEntry 0 k.succ + combinedEntry k.succ 0) +
        ∑ k : Fin 6, ∑ l : Fin 6, combinedEntry k.succ l.succ := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp_rw [Fin.sum_univ_succ]
  rw [Finset.sum_add_distrib]
  ring

/-- Exact reduction of all 49 entries to the algebraic diagonal and the six
periodic diagonal corrections. -/
theorem closed_masses_eq_compact :
    closedWindowSquareMass + closedWindowDistanceMass =
      Real.sin (Real.sqrt 2 / 2) ^ 2 +
        Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) *
          Real.cos (Real.sqrt 2 / 2) + periodicCorrection := by
  rw [closed_masses_eq_entry_sum, entry_sum_decomposition,
    combinedEntry_zero_zero, mixed_entries_sum, periodic_block_eq_correction]
  ring

private lemma sinc_sqrt_two_half :
    Real.sinc (Real.sqrt 2 / 2) =
      2 * Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 := by
  rw [Real.sinc_of_ne_zero (div_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne'
    (by norm_num))]
  ring

theorem closedKernel_zero_eq :
    CurrentKernelFormula.closedKernel 0 =
      2 * Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 := by
  unfold CurrentKernelFormula.closedKernel
  have z1 := sinc_pi_mul_eq_zero 1 (by norm_num)
  have z2 := sinc_pi_mul_eq_zero 2 (by norm_num)
  have z3 := sinc_pi_mul_eq_zero 3 (by norm_num)
  have z4 := sinc_pi_mul_eq_zero 4 (by norm_num)
  have z5 := sinc_pi_mul_eq_zero 5 (by norm_num)
  have z6 := sinc_pi_mul_eq_zero 6 (by norm_num)
  norm_num [CurrentWindow.frequency, CurrentWindow.coefficient,
    Fin.sum_univ_succ, Fin.succ] at z1 z2 z3 z4 z5 z6 ⊢
  ring_nf at z1 z2 z3 z4 z5 z6
  have z2' : Real.sinc (2 * Real.pi) = 0 := by simpa [mul_comm] using z2
  have z3' : Real.sinc (3 * Real.pi) = 0 := by simpa [mul_comm] using z3
  have z4' : Real.sinc (4 * Real.pi) = 0 := by simpa [mul_comm] using z4
  have z5' : Real.sinc (5 * Real.pi) = 0 := by simpa [mul_comm] using z5
  have z6' : Real.sinc (6 * Real.pi) = 0 := by simpa [mul_comm] using z6
  simp only [show 2 * Real.pi * 3 / 2 = 3 * Real.pi by ring,
    show 2 * Real.pi * 4 / 2 = 4 * Real.pi by ring,
    show 2 * Real.pi * 5 / 2 = 5 * Real.pi by ring,
    show 2 * Real.pi * 6 / 2 = 6 * Real.pi by ring]
  rw [z1, z2', z3', z4', z5', z6', sinc_sqrt_two_half]
  ring

theorem closedKernel_zero_sq :
    CurrentKernelFormula.closedKernel 0 ^ 2 =
      2 * Real.sin (Real.sqrt 2 / 2) ^ 2 := by
  rw [closedKernel_zero_eq]
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  nlinarith

end Zeta23Ext.CurrentWindowClosedHAssembly

end
