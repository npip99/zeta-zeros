/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowFiniteCertificate

/-!
# Scalable seams for the current strict `H` certificate

This module keeps each transcendental normalization local to one matrix
entry.  It deliberately does not import `CurrentWindowClosedHCertificate`:
that module's monolithic 49-entry reduction does not cold-build.
-/

noncomputable section

open Real
open scoped BigOperators

namespace Zeta23Ext.CurrentWindowClosedHScalable

open CurrentWindow
open CurrentWindowFiniteCertificate

private lemma sinc_sqrt_two_half :
    Real.sinc (Real.sqrt 2 / 2) =
      2 * Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 := by
  rw [Real.sinc_of_ne_zero (div_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne'
    (by norm_num))]
  ring

private lemma sinc_sqrt_two :
    Real.sinc (Real.sqrt 2) =
      2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) /
        Real.sqrt 2 := by
  rw [Real.sinc_of_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne']
  rw [show Real.sqrt 2 = Real.sqrt 2 / 2 + Real.sqrt 2 / 2 by ring,
    Real.sin_add]
  ring

private lemma sinc_pi_mul_eq_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sinc (Real.pi * k) = 0 := by
  rw [show Real.pi * (k : ℝ) = (k : ℝ) * Real.pi by ring,
    Real.sinc_of_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hk) Real.pi_ne_zero),
    Real.sin_nat_mul_pi]
  norm_num

private lemma half_sqrt_two_sub_nat_pi_ne_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sqrt 2 / 2 - k * Real.pi ≠ 0 := by
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hp := Real.pi_gt_three
  intro h
  nlinarith

private lemma half_sqrt_two_add_nat_pi_ne_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sqrt 2 / 2 + k * Real.pi ≠ 0 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hp := Real.pi_pos
  have hs := Real.sqrt_nonneg 2
  positivity

private lemma sinc_half_sub_periodic (k : ℕ) (hk : k ≠ 0) :
    Real.sinc (Real.sqrt 2 * (1 / 2 : ℝ) - Real.pi * k) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 - k * Real.pi) := by
  have harg := half_sqrt_two_sub_nat_pi_ne_zero k hk
  rw [show Real.sqrt 2 * (1 / 2 : ℝ) - Real.pi * k =
      Real.sqrt 2 / 2 - k * Real.pi by ring,
    Real.sinc_of_ne_zero harg, Real.sin_sub_nat_mul_pi]

private lemma sinc_half_add_periodic (k : ℕ) (hk : k ≠ 0) :
    Real.sinc (Real.sqrt 2 * (1 / 2 : ℝ) + Real.pi * k) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 + k * Real.pi) := by
  have harg := half_sqrt_two_add_nat_pi_ne_zero k hk
  rw [show Real.sqrt 2 * (1 / 2 : ℝ) + Real.pi * k =
      Real.sqrt 2 / 2 + k * Real.pi by ring,
    Real.sinc_of_ne_zero harg, Real.sin_add_nat_mul_pi]

private lemma sinc_root_sub_periodic (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((Real.sqrt 2 - 2 * Real.pi * k) / 2) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 - k * Real.pi) := by
  convert sinc_half_sub_periodic k hk using 1 <;> ring

private lemma sinc_root_add_periodic (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((Real.sqrt 2 + 2 * Real.pi * k) / 2) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 + k * Real.pi) := by
  convert sinc_half_add_periodic k hk using 1 <;> ring

private lemma sinc_periodic_sub_root (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((2 * Real.pi * k - Real.sqrt 2) / 2) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 - k * Real.pi) := by
  rw [show (2 * Real.pi * k - Real.sqrt 2) / 2 =
      -((Real.sqrt 2 - 2 * Real.pi * k) / 2) by ring,
    Real.sinc_neg, sinc_root_sub_periodic k hk]

private lemma sinc_periodic_add_root (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((2 * Real.pi * k + Real.sqrt 2) / 2) =
      (-1 : ℝ) ^ k * Real.sin (Real.sqrt 2 / 2) /
        (Real.sqrt 2 / 2 + k * Real.pi) := by
  rw [add_comm, sinc_root_add_periodic k hk]

private lemma sinc_periodic_half_eq_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sinc (2 * Real.pi * k / 2) = 0 := by
  convert sinc_pi_mul_eq_zero k hk using 1 <;> ring

private lemma sqrt_two_sub_two_pi_mul_ne_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sqrt 2 - 2 * Real.pi * k ≠ 0 := by
  intro h
  apply half_sqrt_two_sub_nat_pi_ne_zero k hk
  linarith

private lemma sqrt_two_add_two_pi_mul_ne_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sqrt 2 + 2 * Real.pi * k ≠ 0 := by
  intro h
  apply half_sqrt_two_add_nat_pi_ne_zero k hk
  linarith

/-- One summand of the square mass plus the corresponding summand of the
distance mass. -/
def combinedEntry (i j : Fin 7) : ℝ :=
  coefficient i * coefficient j * cosCosIntegral (frequency i) (frequency j) +
    coefficient i * coefficient j * absKernelIntegral (frequency i) (frequency j)

/-- Pure rearrangement: no transcendental reasoning is hidden in the
entrywise architecture. -/
theorem closed_masses_eq_entry_sum :
    closedWindowSquareMass + closedWindowDistanceMass =
      ∑ i : Fin 7, ∑ j : Fin 7, combinedEntry i j := by
  unfold closedWindowSquareMass closedWindowDistanceMass combinedEntry cosCosIntegral
  simp_rw [Finset.sum_add_distrib]
  ring

/-- The algebraic-frequency diagonal entry, reduced independently of the
other 48 entries. -/
theorem combinedEntry_zero_zero :
    combinedEntry 0 0 = Real.sin (Real.sqrt 2 / 2) ^ 2 +
      Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) *
        Real.cos (Real.sqrt 2 / 2) := by
  unfold combinedEntry absKernelIntegral cosCosIntegral
  norm_num [coefficient, frequency, sinc_sqrt_two_half, sinc_sqrt_two]
  field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [hs]

/-- A representative diagonal entry of the periodic block.  Every other
periodic diagonal has the same proof with its concrete index. -/
theorem combinedEntry_one_one :
    combinedEntry 1 1 =
      (3322500 / 1000000000 : ℝ) ^ 2 *
        (1 / 2 - 1 / (4 * Real.pi ^ 2)) := by
  have z1 := sinc_pi_mul_eq_zero 1 (by norm_num)
  have z2 := sinc_pi_mul_eq_zero 2 (by norm_num)
  norm_num at z1 z2
  unfold combinedEntry absKernelIntegral cosCosIntegral
  norm_num [coefficient, frequency]
  ring_nf at z1 z2 ⊢
  rw [z1, z2]
  field_simp [Real.pi_ne_zero]
  ring

/-- A representative off-diagonal entry of the periodic block. -/
theorem combinedEntry_one_two : combinedEntry 1 2 = 0 := by
  have z1 := sinc_pi_mul_eq_zero 1 (by norm_num)
  have z2 := sinc_pi_mul_eq_zero 2 (by norm_num)
  have z3 := sinc_pi_mul_eq_zero 3 (by norm_num)
  norm_num at z1 z2 z3
  unfold combinedEntry absKernelIntegral cosCosIntegral
  norm_num [coefficient, frequency]
  ring_nf at z1 z2 z3 ⊢
  simp only [Real.sinc_neg, z1, z3]
  ring

private def periodicDiagonal (k : Fin 6) : ℝ :=
  match k.1 with
  | 0 => (3322500 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (4 * Real.pi ^ 2))
  | 1 => (-7609135 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (16 * Real.pi ^ 2))
  | 2 => (1190194 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (36 * Real.pi ^ 2))
  | 3 => (-731476 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (64 * Real.pi ^ 2))
  | 4 => (-1680572 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (100 * Real.pi ^ 2))
  | _ => (1141360 / 1000000000 : ℝ) ^ 2 * (1 / 2 - 1 / (144 * Real.pi ^ 2))

/-- All 36 periodic entries at once: the block is exactly diagonal.  The
concrete zero witnesses are normalized before the case split, so each branch
contains only rational ring arithmetic. -/
theorem combinedEntry_periodic (k l : Fin 6) :
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

theorem periodic_block_sum :
    (∑ k : Fin 6, ∑ l : Fin 6, combinedEntry k.succ l.succ) =
      ∑ k : Fin 6, periodicDiagonal k := by
  simp_rw [combinedEntry_periodic]
  simp

private lemma mixed_pair_one : combinedEntry 0 1 + combinedEntry 1 0 = 0 := by
  have rm := sinc_root_sub_periodic 1 (by norm_num)
  have rp := sinc_root_add_periodic 1 (by norm_num)
  have pm := sinc_periodic_sub_root 1 (by norm_num)
  have pp := sinc_periodic_add_root 1 (by norm_num)
  have zh := sinc_periodic_half_eq_zero 1 (by norm_num)
  norm_num at rm rp pm pp zh
  unfold combinedEntry absKernelIntegral cosCosIntegral
  norm_num [coefficient, frequency, sinc_sqrt_two_half]
  simp only [rm, rp, pm, pp, zh]
  have dm := sqrt_two_sub_two_pi_mul_ne_zero 1 (by norm_num)
  have dp := sqrt_two_add_two_pi_mul_ne_zero 1 (by norm_num)
  ring_nf at dm dp
  field_simp [Real.pi_ne_zero, sqrt_two_sub_two_pi_mul_ne_zero,
    sqrt_two_add_two_pi_mul_ne_zero, dm, dp,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  ring_nf
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma mixed_pair_two : combinedEntry 0 2 + combinedEntry 2 0 = 0 := by
  have rm := sinc_root_sub_periodic 2 (by norm_num)
  have rp := sinc_root_add_periodic 2 (by norm_num)
  have pm := sinc_periodic_sub_root 2 (by norm_num)
  have pp := sinc_periodic_add_root 2 (by norm_num)
  have zh := sinc_periodic_half_eq_zero 2 (by norm_num)
  norm_num at rm rp pm pp zh
  unfold combinedEntry absKernelIntegral cosCosIntegral
  norm_num [coefficient, frequency, sinc_sqrt_two_half]
  simp only [rm, rp, pm, pp, zh]
  have dm := sqrt_two_sub_two_pi_mul_ne_zero 2 (by norm_num)
  have dp := sqrt_two_add_two_pi_mul_ne_zero 2 (by norm_num)
  ring_nf at dm dp
  field_simp [Real.pi_ne_zero, sqrt_two_sub_two_pi_mul_ne_zero,
    sqrt_two_add_two_pi_mul_ne_zero, dm, dp,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  ring_nf
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma mixed_pair_three : combinedEntry 0 3 + combinedEntry 3 0 = 0 := by
  have rm := sinc_root_sub_periodic 3 (by norm_num)
  have rp := sinc_root_add_periodic 3 (by norm_num)
  have pm := sinc_periodic_sub_root 3 (by norm_num)
  have pp := sinc_periodic_add_root 3 (by norm_num)
  have zh := sinc_periodic_half_eq_zero 3 (by norm_num)
  norm_num at rm rp pm pp zh
  unfold combinedEntry absKernelIntegral cosCosIntegral
  norm_num [coefficient, frequency, sinc_sqrt_two_half,
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, mul_comm]
  try simp only [rm, rp, pm, pp, zh]
  have dm := sqrt_two_sub_two_pi_mul_ne_zero 3 (by norm_num)
  have dp := sqrt_two_add_two_pi_mul_ne_zero 3 (by norm_num)
  ring_nf at dm dp
  field_simp [Real.pi_ne_zero, sqrt_two_sub_two_pi_mul_ne_zero,
    sqrt_two_add_two_pi_mul_ne_zero, dm, dp,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  ring_nf
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The final strict arithmetic is independent of how the finite compact
identity and its numerical upper bound are established.  This theorem is the
contract consumed by a completed entry table plus a numerical certificate. -/
theorem strong_closedH_lower_of_compact
    (s q : ℝ) (hs : 0 < s)
    (hmass : closedWindowSquareMass + closedWindowDistanceMass = s ^ 2 + q)
    (hkernel : CurrentKernelFormula.closedKernel 0 ^ 2 = 2 * s ^ 2)
    (hq : q ≤ (165508598 / 100000000 : ℝ) * s ^ 2) :
    (67245701 / 100000000 : ℝ) ≤ closedH := by
  rw [closedH, hmass, hkernel]
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hden : 0 < 2 * s ^ 2 := by positivity
  rw [le_sub_iff_add_le]
  have hratio : (s ^ 2 + q) / (2 * s ^ 2) ≤
      (132754299 / 100000000 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  linarith

end Zeta23Ext.CurrentWindowClosedHScalable

end
