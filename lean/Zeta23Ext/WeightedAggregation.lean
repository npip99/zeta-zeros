/-
Zeta23Ext/WeightedAggregation.lean

The purely finite weighted seven-window bookkeeping used by the
`509/100000` argument.  This file deliberately does not import or assert a
numerical certificate for the local inequality: that inequality is an
explicit hypothesis of `weighted_window_sum_nat` and
`weighted_window_summation`.
-/
import Zeta23Ext.Aggregation

noncomputable section
set_option maxHeartbeats 1000000

open Finset
open scoped BigOperators

namespace Zeta23Ext.Weighted

/-! ## Exact data -/

/-- The numerator of the exact pair weight `a i j`, whose denominator is
`10^6`.  Values outside `0 <= i < j <= 6` are zero. -/
def pairWeightNumerator : ℕ → ℕ → ℕ
  | 0, 1 => 239252
  | 0, 2 => 528172
  | 0, 3 => 965879
  | 0, 4 => 1000000
  | 0, 5 => 1000000
  | 0, 6 => 2000000
  | 1, 2 => 381335
  | 1, 3 => 465776
  | 1, 4 => 34121
  | 1, 5 => 0
  | 1, 6 => 1000000
  | 2, 3 => 379413
  | 2, 4 => 12104
  | 2, 5 => 34121
  | 2, 6 => 1000000
  | 3, 4 => 379413
  | 3, 5 => 465776
  | 3, 6 => 965879
  | 4, 5 => 381335
  | 4, 6 => 528172
  | 5, 6 => 239252
  | _, _ => 0

/-- The exact rational pair weight `a_{ij}`. -/
def pairWeight (i j : ℕ) : ℝ := pairWeightNumerator i j / 1000000

/-- The pressure coefficient in the local functional. -/
def pressure : ℝ := 1 / 2300

/-- The certified target used by the paper. -/
def beta : ℝ := 509 / 100000

/-- The block length used by the paper. -/
def blockLength : ℕ := 250

/-- `A = beta * (250 - 6)`. -/
def blockTarget : ℝ := 31049 / 25000

lemma pairWeight_nonneg (i j : ℕ) : 0 ≤ pairWeight i j := by
  unfold pairWeight
  positivity

/-- Every one of the six span capacities is exactly two. -/
lemma pairWeight_capacity {r : ℕ} (hr1 : 1 ≤ r) (hr6 : r ≤ 6) :
    ∑ i ∈ Finset.range (7 - r), pairWeight i (i + r) = 2 := by
  interval_cases r <;>
    norm_num [Finset.sum_range_succ, pairWeight, pairWeightNumerator]

lemma pressure_nonneg : 0 ≤ pressure := by norm_num [pressure]
lemma pressure_six : 6 * pressure = 3 / 1150 := by norm_num [pressure]
lemma beta_blockLength : beta * ((blockLength : ℝ) - 6) = blockTarget := by
  norm_num [beta, blockLength, blockTarget]

/-! ## A generic weighted local functional -/

/-- Seven-point functional for an arbitrary nonnegative position-dependent
pair-weight table `a`.  The inner gap sum represents `y_j-y_i`. -/
def F6With (p : ℝ) (a : ℕ → ℕ → ℝ) (w : ℝ → ℝ)
    (g : Fin 6 → ℝ) : ℝ :=
  p * (∑ i, g i) +
    ∑ r ∈ Finset.Icc (1 : ℕ) 6,
      ∑ i ∈ Finset.range (7 - r),
        a i (i + r) * w (∑ t ∈ Finset.Ico i (i + r), Aggregation.gext g t)

/-- The exact local functional in the paper. -/
def F6 (w : ℝ → ℝ) (g : Fin 6 → ℝ) : ℝ :=
  F6With pressure pairWeight w g

lemma F6With_gwin (p : ℝ) (a : ℕ → ℕ → ℝ) (w : ℝ → ℝ)
    (Y : ℕ → ℝ) (k : ℕ) :
    F6With p a w (Aggregation.gwin Y k)
      = p * (Y (k + 6) - Y k) +
        ∑ r ∈ Finset.Icc (1 : ℕ) 6,
          ∑ i ∈ Finset.range (7 - r),
            a i (i + r) * w (Y (k + i + r) - Y (k + i)) := by
  unfold F6With
  rw [Aggregation.sum_gwin]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_Icc] at hr
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Aggregation.warg_gwin Y k i r (by omega)]

/-! ## Windows to a block -/

/-- Weighted shifted-window bookkeeping for one fixed span `r`.  It is
stated separately so other exact tables can reuse the proof. -/
lemma weighted_span_sum_le {a : ℕ → ℕ → ℝ}
    (ha : ∀ i j, 0 ≤ a i j) {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    {m r : ℕ} (hm : 7 ≤ m) (hr1 : 1 ≤ r) (hr6 : r ≤ 6)
    (hcap : ∑ i ∈ Finset.range (7 - r), a i (i + r) ≤ 2)
    (Y : ℕ → ℝ) :
    ∑ k ∈ Finset.range (m - 6),
        ∑ i ∈ Finset.range (7 - r),
          a i (i + r) * w (Y (k + i + r) - Y (k + i))
      ≤ 2 * ∑ x ∈ Finset.range (m - r), w (Y (x + r) - Y x) := by
  rw [Finset.sum_comm]
  have hshift : ∀ i ∈ Finset.range (7 - r),
      ∑ k ∈ Finset.range (m - 6), w (Y (k + i + r) - Y (k + i))
        ≤ ∑ x ∈ Finset.range (m - r), w (Y (x + r) - Y x) := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact Aggregation.sum_shift_le
      (f := fun x => w (Y (x + r) - Y x)) (fun x => hw _) (by omega)
  calc
    ∑ i ∈ Finset.range (7 - r),
        ∑ k ∈ Finset.range (m - 6),
          a i (i + r) * w (Y (k + i + r) - Y (k + i))
        = ∑ i ∈ Finset.range (7 - r),
            a i (i + r) *
              (∑ k ∈ Finset.range (m - 6),
                w (Y (k + i + r) - Y (k + i))) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (7 - r),
          a i (i + r) *
            (∑ x ∈ Finset.range (m - r), w (Y (x + r) - Y x)) := by
          exact Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hshift i hi) (ha _ _)
    _ = (∑ i ∈ Finset.range (7 - r), a i (i + r)) *
          (∑ x ∈ Finset.range (m - r), w (Y (x + r) - Y x)) := by
          rw [Finset.sum_mul]
    _ ≤ 2 * ∑ x ∈ Finset.range (m - r), w (Y (x + r) - Y x) := by
          exact mul_le_mul_of_nonneg_right hcap
            (Finset.sum_nonneg fun x _ => hw _)

/-- Purely combinatorial weighted windows-to-block inequality.  If every
nonnegative six-gap vector satisfies the local inequality with target `b`,
and every span capacity is at most two, then summing the `m-6` windows gives

`b(m-6) ≤ 2 Σ_{i<j} w(Y_j-Y_i) + 6p (Y_{m-1}-Y_0)`.
-/
theorem weighted_window_sum_nat {p b : ℝ} {a : ℕ → ℕ → ℝ}
    (hp : 0 ≤ p) (ha : ∀ i j, 0 ≤ a i j)
    (hcap : ∀ r, 1 ≤ r → r ≤ 6 →
      ∑ i ∈ Finset.range (7 - r), a i (i + r) ≤ 2)
    {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hloc : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → b ≤ F6With p a w g)
    {m : ℕ} (hm : 7 ≤ m) {Y : ℕ → ℝ} (hY : Monotone Y) :
    b * ((m : ℝ) - 6)
      ≤ 2 * (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range j, w (Y j - Y i))
        + (6 * p) * (Y (m - 1) - Y 0) := by
  have hg : ∀ k, ∀ i : Fin 6, 0 ≤ Aggregation.gwin Y k i := by
    intro k i
    exact sub_nonneg.mpr (hY (Nat.le_succ (k + i)))
  have hlocalSum : b * ((m : ℝ) - 6)
      ≤ ∑ k ∈ Finset.range (m - 6), F6With p a w (Aggregation.gwin Y k) := by
    have hc : ((m - 6 : ℕ) : ℝ) = (m : ℝ) - 6 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    calc
      b * ((m : ℝ) - 6) = ∑ _k ∈ Finset.range (m - 6), b := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc]
        ring
      _ ≤ _ := Finset.sum_le_sum fun k _ => hloc _ (hg k)
  have hgap : ∑ k ∈ Finset.range (m - 6), (Y (k + 6) - Y k)
      ≤ 6 * (Y (m - 1) - Y 0) := by
    have htel : ∀ k, Y (k + 6) - Y k =
        ∑ s ∈ Finset.range 6, (Y (k + s + 1) - Y (k + s)) := by
      intro k
      have h2 : ∀ s ∈ Finset.range 6, Y (k + s + 1) - Y (k + s)
          = (fun u => Y (k + u)) (s + 1) - (fun u => Y (k + u)) s := by
        intro s _
        simp only
        rw [add_assoc]
      rw [Finset.sum_congr rfl h2, Finset.sum_range_sub (fun u => Y (k + u)) 6]
      simp
    calc
      ∑ k ∈ Finset.range (m - 6), (Y (k + 6) - Y k)
          = ∑ s ∈ Finset.range 6, ∑ k ∈ Finset.range (m - 6),
              (Y (k + s + 1) - Y (k + s)) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => htel k
      _ ≤ ∑ _s ∈ Finset.range 6, ∑ t ∈ Finset.range (m - 1),
              (Y (t + 1) - Y t) := by
            refine Finset.sum_le_sum fun s hs => ?_
            rw [Finset.mem_range] at hs
            exact Aggregation.sum_shift_le
              (f := fun t => Y (t + 1) - Y t)
              (fun t => sub_nonneg.mpr (hY (Nat.le_succ t))) (by omega)
      _ = 6 * (Y (m - 1) - Y 0) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              Finset.sum_range_sub Y (m - 1)]
            norm_num
  have hpGap : p * (∑ k ∈ Finset.range (m - 6), (Y (k + 6) - Y k))
      ≤ (6 * p) * (Y (m - 1) - Y 0) := by
    calc
      p * (∑ k ∈ Finset.range (m - 6), (Y (k + 6) - Y k))
          ≤ p * (6 * (Y (m - 1) - Y 0)) := mul_le_mul_of_nonneg_left hgap hp
      _ = (6 * p) * (Y (m - 1) - Y 0) := by ring
  have hpair :
      ∑ k ∈ Finset.range (m - 6),
        ∑ r ∈ Finset.Icc (1 : ℕ) 6,
          ∑ i ∈ Finset.range (7 - r),
            a i (i + r) * w (Y (k + i + r) - Y (k + i))
      ≤ 2 * (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range j, w (Y j - Y i)) := by
    rw [Finset.sum_comm]
    calc
      ∑ r ∈ Finset.Icc (1 : ℕ) 6,
          ∑ k ∈ Finset.range (m - 6),
            ∑ i ∈ Finset.range (7 - r),
              a i (i + r) * w (Y (k + i + r) - Y (k + i))
          ≤ ∑ r ∈ Finset.Icc (1 : ℕ) 6,
              2 * ∑ x ∈ Finset.range (m - r), w (Y (x + r) - Y x) := by
            refine Finset.sum_le_sum fun r hr => ?_
            rw [Finset.mem_Icc] at hr
            exact weighted_span_sum_le ha hw hm hr.1 hr.2 (hcap r hr.1 hr.2) Y
      _ = 2 * ∑ r ∈ Finset.Icc (1 : ℕ) 6,
              ∑ x ∈ Finset.range (m - r), w (Y (x + r) - Y x) := by
            rw [Finset.mul_sum]
      _ ≤ 2 * (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range j, w (Y j - Y i)) := by
            exact mul_le_mul_of_nonneg_left (Aggregation.sum_pairs_le hw Y m) (by norm_num)
  have hexpand :
      ∑ k ∈ Finset.range (m - 6), F6With p a w (Aggregation.gwin Y k)
        = p * (∑ k ∈ Finset.range (m - 6), (Y (k + 6) - Y k))
          + ∑ k ∈ Finset.range (m - 6),
              ∑ r ∈ Finset.Icc (1 : ℕ) 6,
                ∑ i ∈ Finset.range (7 - r),
                  a i (i + r) * w (Y (k + i + r) - Y (k + i)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => F6With_gwin p a w Y k
  rw [hexpand] at hlocalSum
  linarith

/-- `Fin m` formulation of `weighted_window_sum_nat`, matching the Gram
block API used elsewhere in `Zeta23Ext`. -/
theorem weighted_window_summation {p b : ℝ} {a : ℕ → ℕ → ℝ}
    (hp : 0 ≤ p) (ha : ∀ i j, 0 ≤ a i j)
    (hcap : ∀ r, 1 ≤ r → r ≤ 6 →
      ∑ i ∈ Finset.range (7 - r), a i (i + r) ≤ 2)
    {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hloc : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → b ≤ F6With p a w g)
    {m : ℕ} (hm : 7 ≤ m) {y : Fin m → ℝ} (hy : StrictMono y) :
    b * ((m : ℝ) - 6)
      ≤ Aggregation.Em w y
        + (6 * p) * (y ⟨m - 1, by omega⟩ - y ⟨0, by omega⟩) := by
  set Y : ℕ → ℝ := fun n => y ⟨min n (m - 1), by omega⟩ with hYdef
  have hY : Monotone Y := by
    intro u v huv
    refine hy.monotone ?_
    rw [Fin.mk_le_mk]
    omega
  have hYval : ∀ j : Fin m, Y (j : ℕ) = y j := by
    intro j
    have hj := j.isLt
    show y _ = y j
    congr 1
    apply Fin.ext
    simp only
    omega
  have hEm : Aggregation.Em w y =
      2 * ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range j, w (Y j - Y i) := by
    unfold Aggregation.Em
    congr 1
    have hj : ∀ j : Fin m, ∑ i ∈ Finset.Iio j, w (y j - y i)
        = (fun n => ∑ i ∈ Finset.range n, w (Y n - Y i)) (j : ℕ) := by
      intro j
      simp only
      calc
        ∑ i ∈ Finset.Iio j, w (y j - y i)
            = ∑ i ∈ Finset.Iio j, (fun n => w (Y (j : ℕ) - Y n)) (i : ℕ) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                simp only
                rw [hYval i, hYval j]
        _ = ∑ i ∈ Finset.range (j : ℕ), w (Y (j : ℕ) - Y i) :=
              Aggregation.sum_Iio_fin (by omega) j
                (fun n => w (Y (j : ℕ) - Y n))
    rw [Finset.sum_congr rfl fun j _ => hj j]
    exact Fin.sum_univ_eq_sum_range
      (fun j => ∑ i ∈ Finset.range j, w (Y j - Y i)) m
  have hend1 : y ⟨m - 1, by omega⟩ = Y (m - 1) :=
    (hYval ⟨m - 1, by omega⟩).symm
  have hend0 : y ⟨0, by omega⟩ = Y 0 := (hYval ⟨0, by omega⟩).symm
  rw [hEm, hend1, hend0]
  exact weighted_window_sum_nat hp ha hcap hw hloc hm hY

/-- The exact table/pressure specialization of `weighted_window_sum_nat`.
The local `509/100000` inequality remains an explicit hypothesis. -/
theorem paper_window_sum_nat {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hloc : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → beta ≤ F6 w g)
    {m : ℕ} (hm : 7 ≤ m) {Y : ℕ → ℝ} (hY : Monotone Y) :
    beta * ((m : ℝ) - 6)
      ≤ 2 * (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range j, w (Y j - Y i))
        + (3 / 1150) * (Y (m - 1) - Y 0) := by
  have h := weighted_window_sum_nat pressure_nonneg pairWeight_nonneg
    (fun r hr1 hr6 => (pairWeight_capacity hr1 hr6).le) hw hloc hm hY
  rwa [pressure_six] at h

/-- At block length `250`, the left side is exactly `A=31049/25000`. -/
theorem paper_window_sum_250 {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hloc : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → beta ≤ F6 w g)
    {Y : ℕ → ℝ} (hY : Monotone Y) :
    blockTarget
      ≤ 2 * (∑ j ∈ Finset.range blockLength,
          ∑ i ∈ Finset.range j, w (Y j - Y i))
        + (3 / 1150) * (Y (blockLength - 1) - Y 0) := by
  have h := paper_window_sum_nat hw hloc (m := blockLength) (by norm_num [blockLength]) hY
  rwa [beta_blockLength] at h

/-- The exact block inequality in the paper, for a strictly increasing
`Fin 250` configuration and `E_m = 2 Σ_{i<j} w(y_j-y_i)`. -/
theorem paper_window_summation_250 {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hloc : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → beta ≤ F6 w g)
    {y : Fin blockLength → ℝ} (hy : StrictMono y) :
    blockTarget ≤ Aggregation.Em w y
      + (3 / 1150) *
        (y ⟨blockLength - 1, by norm_num [blockLength]⟩ -
          y ⟨0, by norm_num [blockLength]⟩) := by
  have h := weighted_window_summation pressure_nonneg pairWeight_nonneg
    (fun r hr1 hr6 => (pairWeight_capacity hr1 hr6).le) hw hloc
    (m := blockLength) (by norm_num [blockLength]) hy
  rwa [beta_blockLength, pressure_six] at h

end Zeta23Ext.Weighted
