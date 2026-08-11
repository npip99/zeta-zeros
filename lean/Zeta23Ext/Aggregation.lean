/-
Zeta23Ext/Aggregation.lean — aggregation of the certified 7-point inequality into a
Gram-defect bound (paper Lemmas 4.2, 4.3, 5, and the arithmetic endgame (4.6)→(4.7)).

Self-contained on top of the existing library:
* reuses `RHLinalg` (specMap, rtrace_specMap, frobSq, frobSq_hermitian_eq_sum_sq_eigenvalues, …)
* reuses `Zeta23.ZeroSide.RankTraceMult` (gc, its convexity lemmas,
  sum_gc_diag_le_sum_gc_eigenvalues, sum_eigenvalues_comm).
-/
import Zeta23.ZeroSide.RankTraceMult

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Matrix Finset Unitary
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Aggregation

open RHLinalg Zeta23.ZeroSide.RankTraceMult

/-! ### The arithmetic endgame (paper (4.6) → (4.7)) -/

/-- From `S ≥ H₀·N + Δ` and `Δ ≥ a·S − b·N` with `a < 1`, conclude
`S ≥ ((H₀ − b)/(1 − a))·N`. -/
theorem endgame {S N Δ H₀ a b : ℝ} (ha : a < 1)
    (h1 : H₀ * N + Δ ≤ S) (h2 : a * S - b * N ≤ Δ) :
    ((H₀ - b) / (1 - a)) * N ≤ S := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-! ### Lemma 4.2 (window summation) -/

/-- Extension of `g : Fin 6 → ℝ` to `ℕ` by zero. -/
def gext (g : Fin 6 → ℝ) (t : ℕ) : ℝ := if h : t < 6 then g ⟨t, h⟩ else 0

/-- The seven-point functional `F₆`: for a window with gap vector `g`,
`F₆(g) = (1/3000)·Σᵢ gᵢ + Σ_{r=1}^{6} (2/(7−r)) Σ_{i=0}^{6−r} w(gᵢ + ⋯ + g_{i+r−1})`. -/
def F6 (w : ℝ → ℝ) (g : Fin 6 → ℝ) : ℝ :=
  (1 / 3000) * (∑ i, g i) +
    ∑ r ∈ Finset.Icc (1 : ℕ) 6, (2 / (7 - (r : ℝ))) *
      ∑ i ∈ Finset.range (7 - r), w (∑ t ∈ Finset.Ico i (i + r), gext g t)

/-- Gap vector of the 7-point window starting at position `k` of `Y : ℕ → ℝ`. -/
def gwin (Y : ℕ → ℝ) (k : ℕ) : Fin 6 → ℝ := fun i => Y (k + i + 1) - Y (k + i)

lemma gext_gwin (Y : ℕ → ℝ) (k : ℕ) {t : ℕ} (ht : t < 6) :
    gext (gwin Y k) t = Y (k + t + 1) - Y (k + t) := by
  simp [gext, gwin, ht]

lemma sum_gwin (Y : ℕ → ℝ) (k : ℕ) : ∑ i, gwin Y k i = Y (k + 6) - Y k := by
  simp only [gwin]
  rw [Fin.sum_univ_eq_sum_range (fun t => Y (k + t + 1) - Y (k + t)) 6]
  have h2 : ∀ t ∈ Finset.range 6, Y (k + t + 1) - Y (k + t)
      = (fun s => Y (k + s)) (t + 1) - (fun s => Y (k + s)) t := by
    intro t _
    simp only
    rw [add_assoc]
  rw [Finset.sum_congr rfl h2, Finset.sum_range_sub (fun s => Y (k + s)) 6]
  simp

lemma warg_gwin (Y : ℕ → ℝ) (k i r : ℕ) (hir : i + r ≤ 6) :
    ∑ t ∈ Finset.Ico i (i + r), gext (gwin Y k) t = Y (k + i + r) - Y (k + i) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h6 : i + r - i = r := by omega
  rw [h6]
  have h2 : ∀ s ∈ Finset.range r, gext (gwin Y k) (i + s)
      = (fun u => Y (k + i + u)) (s + 1) - (fun u => Y (k + i + u)) s := by
    intro s hs
    rw [Finset.mem_range] at hs
    rw [gext_gwin Y k (show i + s < 6 by omega)]
    simp only
    have e1 : k + (i + s) + 1 = k + i + (s + 1) := by omega
    have e2 : k + (i + s) = k + i + s := by omega
    rw [e1, e2]
  rw [Finset.sum_congr rfl h2, Finset.sum_range_sub (fun u => Y (k + i + u)) r]
  simp

lemma F6_gwin (w : ℝ → ℝ) (Y : ℕ → ℝ) (k : ℕ) :
    F6 w (gwin Y k)
      = (1 / 3000) * (Y (k + 6) - Y k) +
        ∑ r ∈ Finset.Icc (1 : ℕ) 6, (2 / (7 - (r : ℝ))) *
          ∑ i ∈ Finset.range (7 - r), w (Y (k + i + r) - Y (k + i)) := by
  unfold F6
  rw [sum_gwin]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_Icc] at hr
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [warg_gwin Y k i r (by omega)]

/-- Shifted sums are dominated by the full sum (for nonnegative terms). -/
lemma sum_shift_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {n N i : ℕ} (h : n + i ≤ N) :
    ∑ k ∈ Finset.range n, f (k + i) ≤ ∑ a ∈ Finset.range N, f a := by
  have h1 : ∑ a ∈ Finset.Ico i (i + n), f a = ∑ k ∈ Finset.range n, f (k + i) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h2 : i + n - i = n := by omega
    rw [h2]
    exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm i k]
  rw [← h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun a _ _ => hf a
  intro a ha
  rw [Finset.mem_Ico] at ha
  rw [Finset.mem_range]
  omega

/-- Every pair `(a, a+r)` with `1 ≤ r ≤ 6` occurs among the pairs `a < b < m`. -/
lemma sum_pairs_le {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x) (Y : ℕ → ℝ) (m : ℕ) :
    ∑ r ∈ Finset.Icc (1 : ℕ) 6, ∑ a ∈ Finset.range (m - r), w (Y (a + r) - Y a)
      ≤ ∑ b ∈ Finset.range m, ∑ a ∈ Finset.range b, w (Y b - Y a) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  have hinj : ∀ p ∈ (Finset.Icc (1 : ℕ) 6).sigma (fun r => Finset.range (m - r)),
      ∀ q ∈ (Finset.Icc (1 : ℕ) 6).sigma (fun r => Finset.range (m - r)),
      (fun p : (_ : ℕ) × ℕ => (⟨p.2 + p.1, p.2⟩ : (_ : ℕ) × ℕ)) p
        = (fun p : (_ : ℕ) × ℕ => (⟨p.2 + p.1, p.2⟩ : (_ : ℕ) × ℕ)) q → p = q := by
    rintro ⟨r, a⟩ - ⟨r', a'⟩ - h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h ⊢
    omega
  have himage : ∑ q ∈ ((Finset.Icc (1 : ℕ) 6).sigma (fun r => Finset.range (m - r))).image
        (fun p : (_ : ℕ) × ℕ => (⟨p.2 + p.1, p.2⟩ : (_ : ℕ) × ℕ)),
          w (Y q.1 - Y q.2)
      = ∑ p ∈ (Finset.Icc (1 : ℕ) 6).sigma (fun r => Finset.range (m - r)),
          w (Y (p.2 + p.1) - Y p.2) :=
    Finset.sum_image (f := fun q : (_ : ℕ) × ℕ => w (Y q.1 - Y q.2)) hinj
  calc ∑ p ∈ (Finset.Icc (1 : ℕ) 6).sigma (fun r => Finset.range (m - r)), w (Y (p.2 + p.1) - Y p.2)
      = ∑ q ∈ ((Finset.Icc (1 : ℕ) 6).sigma (fun r => Finset.range (m - r))).image
          (fun p : (_ : ℕ) × ℕ => (⟨p.2 + p.1, p.2⟩ : (_ : ℕ) × ℕ)),
            w (Y q.1 - Y q.2) := himage.symm
    _ ≤ ∑ q ∈ (Finset.range m).sigma (fun b => Finset.range b), w (Y q.1 - Y q.2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => hw _
        intro q hq
        rw [Finset.mem_image] at hq
        obtain ⟨⟨r, a⟩, hp, rfl⟩ := hq
        simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hp ⊢
        omega

/-- **Lemma 4.2, ℕ-indexed form.** Summing the 7-point inequality over the `m − 6`
consecutive windows of a monotone `Y` yields
`β(m−6) ≤ 2 Σ_{a<b} w(Y_b − Y_a) + (1/500)(Y_{m−1} − Y_0)`. -/
theorem window_sum_nat {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x) {β : ℝ}
    (hβ : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → β ≤ F6 w g)
    {m : ℕ} (hm : 7 ≤ m) {Y : ℕ → ℝ} (hY : Monotone Y) :
    β * ((m : ℝ) - 6)
      ≤ 2 * (∑ b ∈ Finset.range m, ∑ a ∈ Finset.range b, w (Y b - Y a))
        + (1 / 500) * (Y (m - 1) - Y 0) := by
  have hg : ∀ k, ∀ i : Fin 6, 0 ≤ gwin Y k i := by
    intro k i
    exact sub_nonneg.mpr (hY (Nat.le_succ (k + i)))
  -- Step 1: sum the 7-point inequality over all windows
  have h1 : β * ((m : ℝ) - 6) ≤ ∑ k ∈ Finset.range (m - 6), F6 w (gwin Y k) := by
    have hc : ((m - 6 : ℕ) : ℝ) = (m : ℝ) - 6 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    calc β * ((m : ℝ) - 6) = ∑ _k ∈ Finset.range (m - 6), β := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc]
          ring
      _ ≤ _ := Finset.sum_le_sum fun k _ => hβ _ (hg k)
  -- Step 2: expand the windows
  have h2 : ∑ k ∈ Finset.range (m - 6), F6 w (gwin Y k)
      = (1 / 3000) * (∑ k ∈ Finset.range (m - 6), (Y (k + 6) - Y k))
        + ∑ k ∈ Finset.range (m - 6), ∑ r ∈ Finset.Icc (1 : ℕ) 6, (2 / (7 - (r : ℝ))) *
            ∑ i ∈ Finset.range (7 - r), w (Y (k + i + r) - Y (k + i)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => F6_gwin w Y k
  -- Step 3: gap bookkeeping (each gap lies in at most 6 windows)
  have hgap : ∑ k ∈ Finset.range (m - 6), (Y (k + 6) - Y k) ≤ 6 * (Y (m - 1) - Y 0) := by
    have htel : ∀ k, Y (k + 6) - Y k = ∑ s ∈ Finset.range 6, (Y (k + s + 1) - Y (k + s)) := by
      intro k
      have h2' : ∀ s ∈ Finset.range 6, Y (k + s + 1) - Y (k + s)
          = (fun u => Y (k + u)) (s + 1) - (fun u => Y (k + u)) s := by
        intro s _
        simp only
        rw [add_assoc]
      rw [Finset.sum_congr rfl h2', Finset.sum_range_sub (fun u => Y (k + u)) 6]
      simp
    calc ∑ k ∈ Finset.range (m - 6), (Y (k + 6) - Y k)
        = ∑ k ∈ Finset.range (m - 6), ∑ s ∈ Finset.range 6, (Y (k + s + 1) - Y (k + s)) :=
          Finset.sum_congr rfl fun k _ => htel k
      _ = ∑ s ∈ Finset.range 6, ∑ k ∈ Finset.range (m - 6), (Y (k + s + 1) - Y (k + s)) :=
          Finset.sum_comm
      _ ≤ ∑ s ∈ Finset.range 6, ∑ t ∈ Finset.range (m - 1), (Y (t + 1) - Y t) := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [Finset.mem_range] at hs
          exact sum_shift_le (f := fun t => Y (t + 1) - Y t)
            (fun t => sub_nonneg.mpr (hY (Nat.le_succ t))) (by omega)
      _ = 6 * ∑ t ∈ Finset.range (m - 1), (Y (t + 1) - Y t) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
      _ = 6 * (Y (m - 1) - Y 0) := by rw [Finset.sum_range_sub Y (m - 1)]
  -- Step 4: pair bookkeeping (a pair spanning r gaps lies in ≤ 7−r windows)
  have hwsum : ∑ k ∈ Finset.range (m - 6), ∑ r ∈ Finset.Icc (1 : ℕ) 6, (2 / (7 - (r : ℝ))) *
      ∑ i ∈ Finset.range (7 - r), w (Y (k + i + r) - Y (k + i))
      ≤ 2 * ∑ b ∈ Finset.range m, ∑ a ∈ Finset.range b, w (Y b - Y a) := by
    rw [Finset.sum_comm]
    have hstep : ∀ r ∈ Finset.Icc (1 : ℕ) 6,
        ∑ k ∈ Finset.range (m - 6), (2 / (7 - (r : ℝ))) *
          ∑ i ∈ Finset.range (7 - r), w (Y (k + i + r) - Y (k + i))
        ≤ 2 * ∑ a ∈ Finset.range (m - r), w (Y (a + r) - Y a) := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      have hr7 : (0 : ℝ) < 7 - (r : ℝ) := by
        have : (r : ℝ) ≤ 6 := by exact_mod_cast hr.2
        linarith
      rw [← Finset.mul_sum]
      have hinner : ∑ k ∈ Finset.range (m - 6), ∑ i ∈ Finset.range (7 - r),
          w (Y (k + i + r) - Y (k + i))
          ≤ ((7 - r : ℕ) : ℝ) * ∑ a ∈ Finset.range (m - r), w (Y (a + r) - Y a) := by
        rw [Finset.sum_comm]
        calc ∑ i ∈ Finset.range (7 - r), ∑ k ∈ Finset.range (m - 6),
            w (Y (k + i + r) - Y (k + i))
            ≤ ∑ _i ∈ Finset.range (7 - r), ∑ a ∈ Finset.range (m - r), w (Y (a + r) - Y a) := by
              refine Finset.sum_le_sum fun i hi => ?_
              rw [Finset.mem_range] at hi
              exact sum_shift_le (f := fun a => w (Y (a + r) - Y a)) (fun a => hw _) (by omega)
          _ = ((7 - r : ℕ) : ℝ) * ∑ a ∈ Finset.range (m - r), w (Y (a + r) - Y a) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc (2 / (7 - (r : ℝ))) * ∑ k ∈ Finset.range (m - 6), ∑ i ∈ Finset.range (7 - r),
          w (Y (k + i + r) - Y (k + i))
          ≤ (2 / (7 - (r : ℝ))) *
            (((7 - r : ℕ) : ℝ) * ∑ a ∈ Finset.range (m - r), w (Y (a + r) - Y a)) :=
            mul_le_mul_of_nonneg_left hinner (div_pos (by norm_num) hr7).le
        _ = 2 * ∑ a ∈ Finset.range (m - r), w (Y (a + r) - Y a) := by
            have h7 : ((7 - r : ℕ) : ℝ) = 7 - (r : ℝ) := by
              rw [Nat.cast_sub (by omega)]
              norm_num
            rw [h7, ← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hr7)]
    calc ∑ r ∈ Finset.Icc (1 : ℕ) 6, ∑ k ∈ Finset.range (m - 6), (2 / (7 - (r : ℝ))) *
        ∑ i ∈ Finset.range (7 - r), w (Y (k + i + r) - Y (k + i))
        ≤ ∑ r ∈ Finset.Icc (1 : ℕ) 6, 2 * ∑ a ∈ Finset.range (m - r), w (Y (a + r) - Y a) :=
          Finset.sum_le_sum hstep
      _ = 2 * ∑ r ∈ Finset.Icc (1 : ℕ) 6, ∑ a ∈ Finset.range (m - r), w (Y (a + r) - Y a) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * ∑ b ∈ Finset.range m, ∑ a ∈ Finset.range b, w (Y b - Y a) := by
          have := sum_pairs_le hw Y m
          linarith
  rw [h2] at h1
  linarith

/-- `E_m := 2 Σ_{i<j} w(y_j − y_i)`. -/
def Em {m : ℕ} (w : ℝ → ℝ) (y : Fin m → ℝ) : ℝ :=
  2 * ∑ j, ∑ i ∈ Finset.Iio j, w (y j - y i)

/-- Sums over `Iio j ⊆ Fin m` are sums over `range j`. -/
lemma sum_Iio_fin {m : ℕ} (hm : 0 < m) (j : Fin m) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.Iio j, f (i : ℕ) = ∑ a ∈ Finset.range (j : ℕ), f a := by
  refine Finset.sum_nbij' (fun i => (i : ℕ))
    (fun a => (⟨min a (m - 1), by omega⟩ : Fin m)) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Iio] at hi
    rw [Finset.mem_range]
    exact hi
  · intro a ha
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Iio]
    have hj := j.isLt
    rw [Fin.lt_def]
    simp only
    omega
  · intro i hi
    have hi' := i.isLt
    apply Fin.ext
    simp only
    omega
  · intro a ha
    rw [Finset.mem_range] at ha
    have hj := j.isLt
    simp only
    omega
  · intro i _
    rfl

/-- **Lemma 4.2 (window summation).** For strictly monotone `y : Fin m → ℝ`, `m ≥ 7`,
given the certified 7-point inequality `β ≤ F₆(g)` for all nonnegative gap vectors `g`,
`E_m + (1/500)(y_{m−1} − y_0) ≥ β(m − 6)`. -/
theorem window_summation {m : ℕ} (hm : 7 ≤ m) {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    {β : ℝ} (hβ : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → β ≤ F6 w g)
    {y : Fin m → ℝ} (hy : StrictMono y) :
    β * ((m : ℝ) - 6)
      ≤ Em w y + (1 / 500) * (y ⟨m - 1, by omega⟩ - y ⟨0, by omega⟩) := by
  set Y : ℕ → ℝ := fun n => y ⟨min n (m - 1), by omega⟩ with hYdef
  have hY : Monotone Y := by
    intro a b hab
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
  have hEm : Em w y = 2 * ∑ b ∈ Finset.range m, ∑ a ∈ Finset.range b, w (Y b - Y a) := by
    unfold Em
    congr 1
    have hj : ∀ j : Fin m, ∑ i ∈ Finset.Iio j, w (y j - y i)
        = (fun b => ∑ a ∈ Finset.range b, w (Y b - Y a)) (j : ℕ) := by
      intro j
      simp only
      calc ∑ i ∈ Finset.Iio j, w (y j - y i)
          = ∑ i ∈ Finset.Iio j, (fun t => w (Y (j : ℕ) - Y t)) (i : ℕ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only
            rw [hYval i, hYval j]
        _ = ∑ a ∈ Finset.range (j : ℕ), w (Y (j : ℕ) - Y a) :=
            sum_Iio_fin (by omega) j (fun t => w (Y (j : ℕ) - Y t))
    rw [Finset.sum_congr rfl fun j _ => hj j]
    exact Fin.sum_univ_eq_sum_range (fun b => ∑ a ∈ Finset.range b, w (Y b - Y a)) m
  have hend1 : y ⟨m - 1, by omega⟩ = Y (m - 1) := (hYval ⟨m - 1, by omega⟩).symm
  have hend0 : y ⟨0, by omega⟩ = Y 0 := (hYval ⟨0, by omega⟩).symm
  rw [hEm, hend1, hend0]
  exact window_sum_nat hw hβ hm hY

/-! ### Ψ and Lemma 4.3 (block defect) -/

/-- `Ψ(t) = (t−1)²` on `(−∞, 2]` and `2t − 3` on `[2, ∞)`; equivalently `Ψ = g_2 + 1`. -/
def Psi (t : ℝ) : ℝ := gc 2 t + 1

lemma Psi_of_le {t : ℝ} (h : t ≤ 2) : Psi t = (t - 1) ^ 2 := by
  rw [Psi, gc_of_le h]
  ring

lemma Psi_of_ge {t : ℝ} (h : 2 ≤ t) : Psi t = 2 * t - 3 := by
  rw [Psi, gc_of_ge h]
  ring

lemma Psi_nonneg (t : ℝ) : 0 ≤ Psi t := by
  rcases le_or_gt t 2 with h | h
  · rw [Psi_of_le h]
    positivity
  · rw [Psi_of_ge h.le]
    linarith

section BlockDefect

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `‖A‖_F² = Σᵢⱼ |Aᵢⱼ|²`, entrywise. -/
lemma frobSq_eq_sum_sq {n : Type*} [Fintype n] (A : Matrix n n 𝕜) :
    frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [RHLinalg.frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul]
  norm_cast

/-- Transpose of a triangular double sum. -/
lemma sum_Iio_swap {m : ℕ} (f : Fin m → Fin m → ℝ) :
    ∑ i, ∑ j ∈ Finset.Iio i, f i j = ∑ i, ∑ j ∈ Finset.Ioi i, f j i := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi,
      true_and] at hp ⊢
    exact hp
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi,
      true_and] at hp ⊢
    exact hp
  · rintro ⟨i, j⟩ -
    rfl
  · rintro ⟨i, j⟩ -
    rfl
  · rintro ⟨i, j⟩ -
    rfl

/-- For a symmetric nonnegative array, twice the strict upper triangle is at most the full sum. -/
lemma two_mul_sum_upper_le {m : ℕ} (f : Fin m → Fin m → ℝ) (hnn : ∀ i j, 0 ≤ f i j)
    (hsym : ∀ i j, f i j = f j i) :
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j ≤ ∑ i, ∑ j, f i j := by
  have hsplit : ∀ i : Fin m,
      ∑ j ∈ Finset.Iio i, f i j + ∑ j ∈ Finset.Ioi i, f i j ≤ ∑ j, f i j := by
    intro i
    rw [← Finset.sum_union (Finset.disjoint_left.mpr fun j hj hj' => by
      rw [Finset.mem_Iio] at hj
      rw [Finset.mem_Ioi] at hj'
      exact absurd hj (not_lt.mpr hj'.le))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hnn i j
  have hswap : ∑ i, ∑ j ∈ Finset.Iio i, f i j = ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
    rw [sum_Iio_swap f]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsym j i
  calc 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j
      = ∑ i, ∑ j ∈ Finset.Iio i, f i j + ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
        rw [hswap]
        ring
    _ = ∑ i, (∑ j ∈ Finset.Iio i, f i j + ∑ j ∈ Finset.Ioi i, f i j) :=
        Finset.sum_add_distrib.symm
    _ ≤ ∑ i, ∑ j, f i j := Finset.sum_le_sum fun i _ => hsplit i

/-- **Lemma 4.3 (block defect).** For PSD Hermitian `G`,
`tr Ψ(G) ≥ min(1, 2 Σ_{i<j} |G_{ij}|²)` (trace via eigenvalues). -/
theorem block_defect {m : ℕ} {G : Matrix (Fin m) (Fin m) 𝕜} (hG : G.PosSemidef) :
    min 1 (2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2) ≤ ∑ i, Psi (hG.1.eigenvalues i) := by
  by_cases hall : ∀ i, hG.1.eigenvalues i ≤ 2
  · -- all eigenvalues ≤ 2 : Ψ(G) = (G − I)², so tr Ψ(G) = ‖G − I‖_F²
    have hGH : (G - 1).IsHermitian := hG.1.sub Matrix.isHermitian_one
    have hPsiSum : ∑ i, Psi (hG.1.eigenvalues i) = ∑ i, (hG.1.eigenvalues i - 1) ^ 2 :=
      Finset.sum_congr rfl fun i _ => Psi_of_le (hall i)
    have hfrob : frobSq (G - 1) = ∑ i, (hG.1.eigenvalues i - 1) ^ 2 := by
      have hexp : (G - 1)ᴴ * (G - 1) = Gᴴ * G - Gᴴ - G + 1 := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
        noncomm_ring
      have h1 : frobSq (G - 1)
          = frobSq G - rtrace G - rtrace G + (Fintype.card (Fin m) : ℝ) := by
        show RCLike.re ((G - 1)ᴴ * (G - 1)).trace = _
        rw [hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, map_add, map_sub,
          map_sub, Matrix.trace_conjTranspose, Matrix.trace_one]
        have hre : RCLike.re (star G.trace) = RCLike.re G.trace := by
          rw [RCLike.star_def, RCLike.conj_re]
        rw [hre]
        simp [RHLinalg.frobSq, RHLinalg.rtrace]
      rw [h1, frobSq_hermitian_eq_sum_sq_eigenvalues hG.1, rtrace_eq_sum_eigenvalues hG.1,
        Fintype.card_fin]
      have hexp2 : ∑ i, (hG.1.eigenvalues i - 1) ^ 2
          = ∑ i, (hG.1.eigenvalues i ^ 2 - hG.1.eigenvalues i - hG.1.eigenvalues i + 1) :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [hexp2, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hoff : 2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2 ≤ frobSq (G - 1) := by
      rw [frobSq_eq_sum_sq]
      have h2 : ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2
          = ∑ i, ∑ j ∈ Finset.Ioi i, ‖(G - 1) i j‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_Ioi] at hj
        rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hj), sub_zero]
      rw [h2]
      refine two_mul_sum_upper_le _ (fun i j => sq_nonneg _) fun i j => ?_
      have happ : star ((G - 1) j i) = (G - 1) i j := by
        conv_rhs => rw [← hGH.eq]
        rw [Matrix.conjTranspose_apply]
      rw [← happ, norm_star]
    calc min 1 (2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2)
        ≤ 2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2 := min_le_right _ _
      _ ≤ frobSq (G - 1) := hoff
      _ = ∑ i, Psi (hG.1.eigenvalues i) := by rw [hfrob, hPsiSum]
  · -- some eigenvalue > 2 : Ψ(λ) = 2λ − 3 > 1 already beats the cap
    push Not at hall
    obtain ⟨k, hk⟩ := hall
    calc min 1 (2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2) ≤ 1 := min_le_left _ _
      _ ≤ Psi (hG.1.eigenvalues k) := by
          rw [Psi_of_ge hk.le]
          linarith
      _ ≤ ∑ i, Psi (hG.1.eigenvalues i) :=
          Finset.single_le_sum (fun i _ => Psi_nonneg _) (Finset.mem_univ k)

/-- Lemma 4.3 in `rtrace ∘ specMap` form: `tr Ψ(G) = Σᵢ Ψ(λᵢ)`. -/
theorem block_defect_rtrace {m : ℕ} {G : Matrix (Fin m) (Fin m) 𝕜} (hG : G.PosSemidef) :
    min 1 (2 * ∑ i, ∑ j ∈ Finset.Ioi i, ‖G i j‖ ^ 2) ≤ rtrace (specMap hG.1 Psi) := by
  rw [rtrace_specMap]
  exact block_defect hG

end BlockDefect

/-! ### Lemma 5 (pinching) -/

section Pinching

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `specMap` only depends on the values of the function on the spectrum. -/
lemma specMap_congr {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f g : ℝ → ℝ} (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    specMap hA f = specMap hA g := by
  unfold RHLinalg.specMap
  exact congrArg _ (congrArg Matrix.diagonal (funext fun i => by rw [h i]))

/-- The spectral square root: `specMap √ · specMap √ = M` for PSD `M`. -/
lemma specMap_sqrt_mul_self {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n 𝕜}
    (hM : M.PosSemidef) : specMap hM.1 Real.sqrt * specMap hM.1 Real.sqrt = M := by
  rw [← specMap_mul]
  have h : specMap hM.1 (Real.sqrt * Real.sqrt) = specMap hM.1 id :=
    specMap_congr hM.1 fun i => by
      simp only [Pi.mul_apply, id_eq]
      exact Real.mul_self_sqrt (hM.eigenvalues_nonneg i)
  rw [h, specMap_id]

/-- Eigenvalue sums only depend on the matrix (proof irrelevance across Hermitian proofs). -/
lemma sum_g_eigenvalues_congr {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n 𝕜} (hAB : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) (g : ℝ → ℝ) :
    ∑ i, g (hA.eigenvalues i) = ∑ i, g (hB.eigenvalues i) := by
  subst hAB
  rfl

lemma star_conj_unitary {n : Type*} [Fintype n] [DecidableEq n] {u D : Matrix n n 𝕜}
    (hu : star u * u = 1) : star u * (u * D * star u) * u = D := by
  calc star u * (u * D * star u) * u = star u * u * (D * (star u * u)) := by
        simp only [mul_assoc]
    _ = D := by rw [hu, one_mul, mul_one]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {γ : ι → Type*}
  [∀ b, Fintype (γ b)] [∀ b, DecidableEq (γ b)]

/-- **Lemma 5 (pinching), `g_c` version, sigma-decomposed index set.**
For PSD `M` over `Σ b, γ b`, the blockwise compressions `M_b = M.submatrix (Sigma.mk b) _`
satisfy `Σ_b tr g_c(M_b) ≤ tr g_c(M)`. -/
theorem pinching_gc {M : Matrix ((b : ι) × γ b) ((b : ι) × γ b) 𝕜} (hM : M.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    ∑ b, ∑ i, gc c ((hM.submatrix (Sigma.mk b)).1.eigenvalues i)
      ≤ ∑ j, gc c (hM.1.eigenvalues j) := by
  classical
  set V : Matrix ((b : ι) × γ b) ((b : ι) × γ b) 𝕜 :=
    Matrix.blockDiagonal'
      (fun b => ((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜))
    with hVdef
  have hVunit : ∀ b,
      star ((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜) *
        ((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜) = 1 :=
    fun b => Unitary.star_mul_self_of_mem ((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary).2
  have hVV : Vᴴ * V = 1 := by
    rw [hVdef, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
      ← Matrix.blockDiagonal'_one]
    congr 1
    funext b
    rw [← Matrix.star_eq_conjTranspose]
    exact hVunit b
  have hVV' : V * Vᴴ = 1 := by
    rw [hVdef, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
      ← Matrix.blockDiagonal'_one]
    congr 1
    funext b
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem ((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary).2
  have hM' : (Vᴴ * M * V).PosSemidef := hM.conjTranspose_mul_mul_same V
  -- each diagonal entry of Vᴴ M V is a block eigenvalue
  have hdiag : ∀ (b : ι) (i : γ b),
      RCLike.re ((Vᴴ * M * V) ⟨b, i⟩ ⟨b, i⟩) = (hM.submatrix (Sigma.mk b)).1.eigenvalues i := by
    intro b i
    have outer : ∀ (N : Matrix ((b : ι) × γ b) ((b : ι) × γ b) 𝕜),
        (N * V) ⟨b, i⟩ ⟨b, i⟩ = ∑ l, N ⟨b, i⟩ ⟨b, l⟩ *
          ((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜) l i := by
      intro N
      rw [Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
      rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b)
        (fun b' _ hb => Finset.sum_eq_zero fun l _ => by
          rw [hVdef, Matrix.blockDiagonal'_apply_ne _ _ _ hb, mul_zero])]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hVdef, Matrix.blockDiagonal'_apply_eq]
    have inner : ∀ (l : γ b), (Vᴴ * M) ⟨b, i⟩ ⟨b, l⟩
        = ∑ k, star (((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary :
            Matrix (γ b) (γ b) 𝕜) k i) * M ⟨b, k⟩ ⟨b, l⟩ := by
      intro l
      rw [Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
      rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b)
        (fun b' _ hb => Finset.sum_eq_zero fun k _ => by
          rw [Matrix.conjTranspose_apply, hVdef, Matrix.blockDiagonal'_apply_ne _ _ _ hb,
            star_zero, zero_mul])]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply, hVdef, Matrix.blockDiagonal'_apply_eq]
    have key : (Vᴴ * M * V) ⟨b, i⟩ ⟨b, i⟩
        = (((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜)ᴴ *
            M.submatrix (Sigma.mk b) (Sigma.mk b) *
            ((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜)) i i := by
      rw [outer (Vᴴ * M)]
      conv_rhs => rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [inner l]
      congr 1
    have hUAU : (((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜))ᴴ *
        M.submatrix (Sigma.mk b) (Sigma.mk b) *
        ((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜)
        = Matrix.diagonal (RCLike.ofReal ∘ (hM.submatrix (Sigma.mk b)).1.eigenvalues) := by
      have hspec := (hM.submatrix (Sigma.mk b)).1.spectral_theorem
      rw [conjStarAlgAut_apply] at hspec
      have h1 : (((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜))ᴴ *
          M.submatrix (Sigma.mk b) (Sigma.mk b) *
          ((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜)
          = (((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜))ᴴ *
            (((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜) *
              Matrix.diagonal (RCLike.ofReal ∘ (hM.submatrix (Sigma.mk b)).1.eigenvalues) *
              star ((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary :
                Matrix (γ b) (γ b) 𝕜)) *
            ((hM.submatrix (Sigma.mk b)).1.eigenvectorUnitary : Matrix (γ b) (γ b) 𝕜) := by
        rw [← hspec]
      rw [h1, ← Matrix.star_eq_conjTranspose]
      exact star_conj_unitary (hVunit b)
    rw [key, hUAU, Matrix.diagonal_apply_eq]
    simp

  calc ∑ b, ∑ i, gc c ((hM.submatrix (Sigma.mk b)).1.eigenvalues i)
      = ∑ x : (b : ι) × γ b, gc c (RCLike.re ((Vᴴ * M * V) x x)) := by
        conv_rhs => rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by
          rw [hdiag b i]
    _ ≤ ∑ x, gc c (hM'.1.eigenvalues x) := sum_gc_diag_le_sum_gc_eigenvalues hM' hc
    _ = ∑ j, gc c (hM.1.eigenvalues j) := by
        have hSH : (specMap hM.1 Real.sqrt).IsHermitian := specMap_isHermitian hM.1 _
        have hSS := specMap_sqrt_mul_self hM
        have hWWH : (Vᴴ * specMap hM.1 Real.sqrt) * (Vᴴ * specMap hM.1 Real.sqrt)ᴴ
            = Vᴴ * M * V := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hSH.eq]
          calc Vᴴ * specMap hM.1 Real.sqrt * (specMap hM.1 Real.sqrt * V)
              = Vᴴ * (specMap hM.1 Real.sqrt * specMap hM.1 Real.sqrt) * V := by
                simp only [mul_assoc]
            _ = Vᴴ * M * V := by rw [hSS]
        have hWHW : (Vᴴ * specMap hM.1 Real.sqrt)ᴴ * (Vᴴ * specMap hM.1 Real.sqrt) = M := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hSH.eq]
          calc specMap hM.1 Real.sqrt * V * (Vᴴ * specMap hM.1 Real.sqrt)
              = specMap hM.1 Real.sqrt * (V * Vᴴ) * specMap hM.1 Real.sqrt := by
                simp only [mul_assoc]
            _ = M := by rw [hVV', mul_one, hSS]
        calc ∑ x, gc c (hM'.1.eigenvalues x)
            = ∑ x, gc c ((Matrix.posSemidef_self_mul_conjTranspose
                (Vᴴ * specMap hM.1 Real.sqrt)).1.eigenvalues x) :=
              sum_g_eigenvalues_congr hWWH.symm _ _ _
          _ = ∑ x, gc c ((Matrix.posSemidef_conjTranspose_mul_self
                (Vᴴ * specMap hM.1 Real.sqrt)).1.eigenvalues x) :=
              sum_eigenvalues_comm _ (gc c) (gc_zero hc)
          _ = ∑ j, gc c (hM.1.eigenvalues j) := sum_g_eigenvalues_congr hWHW _ hM.1 _

/-- `Σᵢ Ψ(fᵢ) = Σᵢ g₂(fᵢ) + card`. -/
lemma sum_Psi_eq {n : Type*} [Fintype n] (f : n → ℝ) :
    ∑ i, Psi (f i) = (∑ i, gc 2 (f i)) + (Fintype.card n : ℝ) := by
  simp only [Psi]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **Lemma 5 (pinching), Ψ version, sigma-decomposed index set.**
`tr Ψ(M) ≥ Σ_b tr Ψ(M_b)`. -/
theorem pinching_trPsi {M : Matrix ((b : ι) × γ b) ((b : ι) × γ b) 𝕜} (hM : M.PosSemidef) :
    ∑ b, ∑ i, Psi ((hM.submatrix (Sigma.mk b)).1.eigenvalues i)
      ≤ ∑ j, Psi (hM.1.eigenvalues j) := by
  have h := pinching_gc hM (c := 2) (by norm_num)
  have hL : ∑ b, ∑ i, Psi ((hM.submatrix (Sigma.mk b)).1.eigenvalues i)
      = (∑ b, ∑ i, gc 2 ((hM.submatrix (Sigma.mk b)).1.eigenvalues i))
        + (Fintype.card ((b : ι) × γ b) : ℝ) := by
    rw [Fintype.card_sigma]
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by
      rw [sum_Psi_eq ((hM.submatrix (Sigma.mk b)).1.eigenvalues)]
  rw [hL, sum_Psi_eq (hM.1.eigenvalues)]
  linarith

/-- Eigenvalue sums (through any `g` with `g 0 = 0`) are invariant under simultaneous
reindexing of rows and columns by an equivalence. -/
lemma sum_g_eigenvalues_submatrix_equiv {n' m' : Type*} [Fintype n'] [DecidableEq n']
    [Fintype m'] [DecidableEq m'] (e : m' ≃ n') {M : Matrix n' n' 𝕜} (hM : M.PosSemidef)
    (g : ℝ → ℝ) (hg : g 0 = 0) :
    ∑ i, g ((hM.submatrix ⇑e).1.eigenvalues i) = ∑ j, g (hM.1.eigenvalues j) := by
  have hSH : (specMap hM.1 Real.sqrt).IsHermitian := specMap_isHermitian hM.1 _
  have hSS := specMap_sqrt_mul_self hM
  have hWH : ((specMap hM.1 Real.sqrt).submatrix id ⇑e)ᴴ
      = (specMap hM.1 Real.sqrt).submatrix ⇑e id := by
    rw [Matrix.conjTranspose_submatrix, hSH.eq]
  have hWWH : (specMap hM.1 Real.sqrt).submatrix id ⇑e *
      ((specMap hM.1 Real.sqrt).submatrix id ⇑e)ᴴ = M := by
    rw [hWH, Matrix.submatrix_mul_equiv (specMap hM.1 Real.sqrt) (specMap hM.1 Real.sqrt) id e id,
      hSS, Matrix.submatrix_id_id]
  have hWHW : ((specMap hM.1 Real.sqrt).submatrix id ⇑e)ᴴ *
      (specMap hM.1 Real.sqrt).submatrix id ⇑e = M.submatrix ⇑e ⇑e := by
    rw [hWH]
    calc (specMap hM.1 Real.sqrt).submatrix ⇑e id * (specMap hM.1 Real.sqrt).submatrix id ⇑e
        = ((specMap hM.1 Real.sqrt) * (specMap hM.1 Real.sqrt)).submatrix ⇑e ⇑e := by
          have h := Matrix.submatrix_mul_equiv (specMap hM.1 Real.sqrt)
            (specMap hM.1 Real.sqrt) (⇑e) (Equiv.refl n') (⇑e)
          simpa using h
      _ = M.submatrix ⇑e ⇑e := by rw [hSS]
  calc ∑ i, g ((hM.submatrix ⇑e).1.eigenvalues i)
      = ∑ i, g ((Matrix.posSemidef_conjTranspose_mul_self
          ((specMap hM.1 Real.sqrt).submatrix id ⇑e)).1.eigenvalues i) :=
        sum_g_eigenvalues_congr hWHW.symm _ _ _
    _ = ∑ j, g ((Matrix.posSemidef_self_mul_conjTranspose
          ((specMap hM.1 Real.sqrt).submatrix id ⇑e)).1.eigenvalues j) :=
        (sum_eigenvalues_comm _ g hg).symm
    _ = ∑ j, g (hM.1.eigenvalues j) := sum_g_eigenvalues_congr hWWH _ hM.1 _

/-- **Lemma 5 for consecutive blocks of `Fin`, `g_c` version.** The blocks are the
consecutive segments of sizes `sz 0, sz 1, …` under `finSigmaFinEquiv`. -/
theorem pinching_gc_fin {K : ℕ} {sz : Fin K → ℕ}
    {M : Matrix (Fin (∑ b, sz b)) (Fin (∑ b, sz b)) 𝕜} (hM : M.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    ∑ b, ∑ i, gc c
        ((hM.submatrix (fun i : Fin (sz b) => finSigmaFinEquiv ⟨b, i⟩)).1.eigenvalues i)
      ≤ ∑ j, gc c (hM.1.eigenvalues j) := by
  have h := pinching_gc (hM.submatrix ⇑(finSigmaFinEquiv (n := sz))) hc
  have hblock : ∀ b : Fin K,
      ∑ i, gc c (((hM.submatrix ⇑(finSigmaFinEquiv (n := sz))).submatrix
          (Sigma.mk b)).1.eigenvalues i)
        = ∑ i, gc c
            ((hM.submatrix (fun i : Fin (sz b) => finSigmaFinEquiv ⟨b, i⟩)).1.eigenvalues i) := by
    intro b
    exact sum_g_eigenvalues_congr
      (Matrix.submatrix_submatrix M ⇑finSigmaFinEquiv ⇑finSigmaFinEquiv
        (Sigma.mk b) (Sigma.mk b)) _ _ _
  have hglobal : ∑ j, gc c ((hM.submatrix ⇑(finSigmaFinEquiv (n := sz))).1.eigenvalues j)
      = ∑ j, gc c (hM.1.eigenvalues j) :=
    sum_g_eigenvalues_submatrix_equiv finSigmaFinEquiv hM (gc c) (gc_zero hc)
  rw [← hglobal]
  refine le_trans (le_of_eq ?_) h
  exact Finset.sum_congr rfl fun b _ => (hblock b).symm

/-- **Lemma 5 for consecutive blocks of `Fin`, Ψ version:** `tr Ψ(M) ≥ Σ_B tr Ψ(M_B)`. -/
theorem pinching_trPsi_fin {K : ℕ} {sz : Fin K → ℕ}
    {M : Matrix (Fin (∑ b, sz b)) (Fin (∑ b, sz b)) 𝕜} (hM : M.PosSemidef) :
    ∑ b, ∑ i, Psi
        ((hM.submatrix (fun i : Fin (sz b) => finSigmaFinEquiv ⟨b, i⟩)).1.eigenvalues i)
      ≤ ∑ j, Psi (hM.1.eigenvalues j) := by
  have h := pinching_gc_fin hM (c := 2) (by norm_num)
  have hL : ∑ b, ∑ i, Psi
      ((hM.submatrix (fun i : Fin (sz b) => finSigmaFinEquiv ⟨b, i⟩)).1.eigenvalues i)
      = (∑ b, ∑ i, gc 2
          ((hM.submatrix (fun i : Fin (sz b) => finSigmaFinEquiv ⟨b, i⟩)).1.eigenvalues i))
        + ((∑ b, sz b : ℕ) : ℝ) := by
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sum_Psi_eq ((hM.submatrix
      (fun i : Fin (sz b) => finSigmaFinEquiv ⟨b, i⟩)).1.eigenvalues), Fintype.card_fin]
  have hR : ∑ j, Psi (hM.1.eigenvalues j)
      = (∑ j, gc 2 (hM.1.eigenvalues j)) + ((∑ b, sz b : ℕ) : ℝ) := by
    rw [sum_Psi_eq (hM.1.eigenvalues), Fintype.card_fin]
  rw [hL, hR]
  linarith

end Pinching

end Zeta23Ext.Aggregation
