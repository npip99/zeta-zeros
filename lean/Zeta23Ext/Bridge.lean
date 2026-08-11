/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23Ext/Bridge.lean — LAYER 1 of the final integration of the Theorem-D extension:
the certified 7-point constant `betaCert = 191/50000` and the ABSTRACT COUNTING THEOREM,
fully sorry-free, at the level of matrix/configuration data.  (This file deliberately
imports only the linear-algebra tracks, not the analytic ones; the kernel glue `w = k²`
and the ζ-side packaging live in Zeta23Ext/Main.lean.)

Given
  (i)   the certified 7-point inequality `β ≤ F₆(w, g)` for an abstract nonnegative kernel
        square `w` (hypothesis `hβ`; the certificate track supplies it for `w = kkernel²`
        at `β = betaCert`),
  (ii)  the kernel-limit conclusion as a hypothesis on the Gram matrix `M = VᴴV` of the
        retained zeros: `‖M_{ij}‖² ≥ w(y_j − y_i) − ε` for near pairs (`j < i + m`),
  (iii) the stability rank–trace inequality (imported from
        Zeta23Ext/StabilityRankTrace.lean, not assumed),
  (iv)  the paper's block/pinching/averaging scheme at block length `m` (Lemmas 4.2, 4.3, 5,
        averaged over the `m` block offsets: `sum_blocks_ge`, `sum_spans_le`,
        `pinching_runs`, `block_lower`, `defect_lower`),
the defect-enhanced counting inequality (paper (2.2) + (4.6))

    S ≥ (2 − κ)·N + (β(m−6)/m)·S − ((m−1)/(500m))·N − errors        (`stability_counting`)

follows, and by the arithmetic endgame ((4.6) → (4.7))

    S ≥ ((2 − κ − (m−1)/(500m)) / (1 − β(m−6)/m))·N − errors        (`stability_counting_ratio`).

At `m = 267`, `β = betaCert = 191/50000` (so `A₀ = β·261 = 49851/50000`) the constants are
    a = A₀/m = 16617/4450000,      b = (m−1)/(500m) = 133/66750,
giving the specialized corollary `stability_counting_certified` with ratio constant

    (2 − κ − 133/66750) / (1 − 16617/4450000).

At the Theorem-D moment constant `κ = 2 − HD 1` this is the headline constant
`stabilityConstD` of Zeta23Ext/Main.lean (≈ 0.67302…, vs HD 1 ≈ 0.67250… for Theorem D).
-/
import Zeta23Ext.Aggregation
import Zeta23Ext.StabilityRankTrace

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Finset Matrix
open scoped ComplexOrder BigOperators

namespace Zeta23Ext

namespace Bridge

/-! ## The certified 7-point constant -/

/-- the certified constant of the 7-point inequality `β ≤ F₆(w, g)` for the
Montgomery–Taylor kernel-square window: `β = 191/50000 = 0.00382`. -/
def betaCert : ℝ := 191 / 50000

lemma betaCert_pos : 0 < betaCert := by unfold betaCert; norm_num

lemma betaCert_eq : betaCert = 191 / 50000 := rfl

/-- The two `Ψ` profiles of the completed tracks agree (both are `g₂ + 1`). -/
lemma Psi_eq : Zeta23Ext.Aggregation.Psi = Zeta23Ext.StabilityRankTrace.Psi := rfl

end Bridge

namespace Stability

open Zeta23Ext.Aggregation RHLinalg
open Zeta23.ZeroSide.RankTraceMult (gc gc_zero)
open Zeta23Ext.StabilityRankTrace (colSq)

/-! ## Layer 1.  The offset-averaged block combinatorics -/

/-- `Σ_{t<m} ⌊(r−t)/m⌋ ≥ r + 1 − m`: each `n ∈ [m, r]` is the right endpoint of exactly one
complete block over all offsets (via `n = c·m + t`, `c ≥ 1`). -/
lemma sum_blocks_ge {m r : ℕ} (hm : 0 < m) (_hmr : m ≤ r) :
    r + 1 - m ≤ ∑ t ∈ Finset.range m, (r - t) / m := by
  have hcard : r + 1 - m = #(Finset.Icc m r) := by rw [Nat.card_Icc]
  have hsig : #((Finset.range m).sigma fun t => Finset.range ((r - t) / m))
      = ∑ t ∈ Finset.range m, (r - t) / m := by
    rw [Finset.card_sigma]
    simp
  rw [hcard, ← hsig]
  refine Finset.card_le_card_of_injOn
    (fun n => ⟨n % m, n / m - 1⟩) ?_ ?_
  · intro n hn
    simp only [Finset.coe_Icc, Set.mem_Icc] at hn
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range]
    have hmod := Nat.mod_lt n hm
    have hdm := Nat.div_add_mod n m
    have h1 : 1 ≤ n / m := (Nat.one_le_div_iff hm).mpr hn.1
    have h2 : n / m ≤ (r - n % m) / m := by
      rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm]
      omega
    exact ⟨hmod, by omega⟩
  · rintro n1 hn1 n2 hn2 heq
    simp only [Finset.coe_Icc, Set.mem_Icc] at hn1 hn2
    have h1 := Nat.div_add_mod n1 m
    have h2 := Nat.div_add_mod n2 m
    have e1 : 1 ≤ n1 / m := (Nat.one_le_div_iff hm).mpr hn1.1
    have e2 : 1 ≤ n2 / m := (Nat.one_le_div_iff hm).mpr hn2.1
    have hfst : n1 % m = n2 % m := congrArg Sigma.fst heq
    have hsnd : n1 / m - 1 = n2 / m - 1 := by
      have := congrArg Sigma.snd heq
      simpa using this
    have hdiv : n1 / m = n2 / m := by omega
    rw [hdiv] at h1
    omega

/-- `Σ_{t<m} Σ_{c<K_t} (Y(t+cm+(m−1)) − Y(t+cm)) ≤ (m−1)(Y(r−1) − Y 0)` for monotone `Y`:
each block span telescopes into unit gaps, and each gap is hit at most once per interior
position `i < m−1`, i.e. at most `m−1` times in total over all offsets. -/
lemma sum_spans_le {m r : ℕ} (hm : 1 ≤ m) {Y : ℕ → ℝ} (hY : Monotone Y) :
    ∑ t ∈ Finset.range m, ∑ c ∈ Finset.range ((r - t) / m),
        (Y (t + c * m + (m - 1)) - Y (t + c * m))
      ≤ ((m : ℝ) - 1) * (Y (r - 1) - Y 0) := by
  have hg : ∀ j, 0 ≤ Y (j + 1) - Y j := fun j => sub_nonneg.mpr (hY (Nat.le_succ j))
  have htel : ∀ t c : ℕ, Y (t + c * m + (m - 1)) - Y (t + c * m)
      = ∑ i ∈ Finset.range (m - 1), (Y (t + c * m + i + 1) - Y (t + c * m + i)) := by
    intro t c
    have h2 : ∀ i ∈ Finset.range (m - 1), Y (t + c * m + i + 1) - Y (t + c * m + i)
        = (fun u => Y (t + c * m + u)) (i + 1) - (fun u => Y (t + c * m + u)) i := by
      intro i _
      simp only
      rw [add_assoc]
    rw [Finset.sum_congr rfl h2, Finset.sum_range_sub (fun u => Y (t + c * m + u)) (m - 1)]
    simp
  simp_rw [htel]
  rw [Finset.sum_sigma' (Finset.range m)
    (fun t => Finset.range ((r - t) / m))
    (fun t c => ∑ i ∈ Finset.range (m - 1), (Y (t + c * m + i + 1) - Y (t + c * m + i)))]
  rw [Finset.sum_sigma' ((Finset.range m).sigma (fun t => Finset.range ((r - t) / m)))
    (fun _p => Finset.range (m - 1))
    (fun p i => Y (p.1 + p.2 * m + i + 1) - Y (p.1 + p.2 * m + i))]
  set dom := (((Finset.range m).sigma (fun t => Finset.range ((r - t) / m))).sigma
      (fun _p => Finset.range (m - 1))) with hdom
  set emb : (Σ _p : (Σ _t : ℕ, ℕ), ℕ) → ℕ × ℕ := fun q => (q.2, q.1.1 + q.1.2 * m + q.2)
    with hemb
  have hinj : Set.InjOn emb dom := by
    rintro ⟨⟨t1, c1⟩, i1⟩ h1 ⟨⟨t2, c2⟩, i2⟩ h2 heq
    simp only [hemb, Prod.mk.injEq] at heq
    obtain ⟨hi, hsum⟩ := heq
    simp only [hdom, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe,
      Finset.mem_range] at h1 h2
    subst hi
    have ht1 : t1 < m := h1.1.1
    have ht2 : t2 < m := h2.1.1
    have hD : t1 + c1 * m = t2 + c2 * m := by omega
    have hu1 : (t1 + c1 * m) % m = t1 ∧ (t1 + c1 * m) / m = c1 := by
      constructor
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht1]
      · rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt ht1, Nat.zero_add]
    have hu2 : (t2 + c2 * m) % m = t2 ∧ (t2 + c2 * m) / m = c2 := by
      constructor
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht2]
      · rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt ht2, Nat.zero_add]
    have ht12 : t1 = t2 := by rw [← hu1.1, ← hu2.1, hD]
    have hc12 : c1 = c2 := by rw [← hu1.2, ← hu2.2, hD]
    subst ht12
    subst hc12
    rfl
  calc ∑ q ∈ dom, (Y (q.1.1 + q.1.2 * m + q.2 + 1) - Y (q.1.1 + q.1.2 * m + q.2))
      = ∑ p ∈ dom.image emb, (Y (p.2 + 1) - Y p.2) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ (Finset.range (m - 1)) ×ˢ (Finset.range (r - 1)), (Y (p.2 + 1) - Y p.2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hg p.2)
        intro p hp
        rw [Finset.mem_image] at hp
        obtain ⟨⟨⟨t, c⟩, i⟩, hq, rfl⟩ := hp
        simp only [hdom, Finset.mem_sigma, Finset.mem_range] at hq
        obtain ⟨⟨ht, hc⟩, hi⟩ := hq
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        refine ⟨hi, ?_⟩
        have h1 : c + 1 ≤ (r - t) / m := hc
        have h2 : (c + 1) * m ≤ (r - t) / m * m := Nat.mul_le_mul_right m h1
        have h3 : (r - t) / m * m ≤ r - t := Nat.div_mul_le_self _ _
        have h4 : (c + 1) * m = c * m + m := by ring
        simp only [hemb]
        omega
    _ = ((m : ℝ) - 1) * (Y (r - 1) - Y 0) := by
        rw [Finset.sum_product]
        have hinner : ∀ _i ∈ Finset.range (m - 1),
            ∑ j ∈ Finset.range (r - 1), (Y (j + 1) - Y j) = Y (r - 1) - Y 0 := by
          intro i _
          rw [Finset.sum_range_sub Y (r - 1)]
        rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          rw [Nat.cast_sub hm]; norm_num
        rw [this]

/-! ## Layer 1.  Pinching along the offset-`t` block partition -/

section Pinching

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The embedding of the `c`-th block of size `m` at offset `t`: index `t + c·m + i`. -/
def blockEmb {r m K t : ℕ} (_hKt : t + K * m ≤ r) (c : Fin K) (i : Fin m) : Fin r :=
  ⟨t + (c : ℕ) * m + (i : ℕ), by
    have h1 : (c : ℕ) + 1 ≤ K := c.isLt
    have h2 : ((c : ℕ) + 1) * m ≤ K * m := Nat.mul_le_mul_right m h1
    have h3 : (i : ℕ) < m := i.isLt
    have h4 : ((c : ℕ) + 1) * m = (c : ℕ) * m + m := by ring
    omega⟩

lemma blockEmb_val {r m K t : ℕ} (hKt : t + K * m ≤ r) (c : Fin K) (i : Fin m) :
    (blockEmb hKt c i : ℕ) = t + (c : ℕ) * m + (i : ℕ) := rfl

/-- Chunk assignment `Fin r → Fin (K+2)`: `0` = prefix `[0,t)`, `1+c` = block `c`
(`[t+cm, t+(c+1)m)`), `K+1` = suffix `[t+Km, r)`. -/
def chunkOf (K t m : ℕ) (hm : 0 < m) {r : ℕ} (x : Fin r) : Fin (K + 2) :=
  if h1 : (x : ℕ) < t then ⟨0, by omega⟩
  else if h2 : (x : ℕ) < t + K * m then
    ⟨1 + ((x : ℕ) - t) / m, by
      have : ((x : ℕ) - t) / m < K := by
        rw [Nat.div_lt_iff_lt_mul hm]
        omega
      omega⟩
  else ⟨K + 1, by omega⟩

lemma chunkOf_blockEmb {r m K t : ℕ} (hm : 0 < m) (hKt : t + K * m ≤ r)
    (c : Fin K) (i : Fin m) :
    chunkOf K t m hm (blockEmb hKt c i)
      = ⟨1 + (c : ℕ), by have := c.isLt; omega⟩ := by
  have hi : (i : ℕ) < m := i.isLt
  have hc : (c : ℕ) < K := c.isLt
  have h2 : ((c : ℕ) + 1) * m ≤ K * m := Nat.mul_le_mul_right m hc
  have h4 : ((c : ℕ) + 1) * m = (c : ℕ) * m + m := by ring
  have hv := blockEmb_val hKt c i
  unfold chunkOf
  rw [dif_neg (by rw [hv]; omega), dif_pos (by rw [hv]; omega)]
  apply Fin.ext
  simp only [hv]
  have h5 : t + (c : ℕ) * m + (i : ℕ) - t = (i : ℕ) + (c : ℕ) * m := by omega
  rw [h5, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hi]
  omega

lemma chunkOf_mem {r m K t : ℕ} (hm : 0 < m) {x : Fin r} {c : Fin K}
    (h : chunkOf K t m hm x = ⟨1 + (c : ℕ), by have := c.isLt; omega⟩) :
    t + (c : ℕ) * m ≤ (x : ℕ) ∧ (x : ℕ) < t + (c : ℕ) * m + m := by
  have hc : (c : ℕ) < K := c.isLt
  unfold chunkOf at h
  by_cases h1 : (x : ℕ) < t
  · rw [dif_pos h1] at h
    have := congrArg Fin.val h
    simp only at this
    omega
  rw [dif_neg h1] at h
  by_cases h2 : (x : ℕ) < t + K * m
  · rw [dif_pos h2] at h
    have hval : 1 + ((x : ℕ) - t) / m = 1 + (c : ℕ) := congrArg Fin.val h
    have hdiv : ((x : ℕ) - t) / m = (c : ℕ) := by omega
    have hdm := Nat.div_add_mod ((x : ℕ) - t) m
    have hmod := Nat.mod_lt ((x : ℕ) - t) hm
    rw [hdiv] at hdm
    have hcomm : m * (c : ℕ) = (c : ℕ) * m := Nat.mul_comm _ _
    omega
  · rw [dif_neg h2] at h
    have := congrArg Fin.val h
    simp only at this
    omega

/-- `Fin m ≃` the fiber of the main chunk `1 + c` under `chunkOf`. -/
def fiberEquiv {r m K t : ℕ} (hm : 0 < m) (hKt : t + K * m ≤ r) (c : Fin K) :
    Fin m ≃ {x : Fin r // chunkOf K t m hm x = ⟨1 + (c : ℕ), by have := c.isLt; omega⟩} where
  toFun i := ⟨blockEmb hKt c i, chunkOf_blockEmb hm hKt c i⟩
  invFun x := ⟨(x : Fin r).val - (t + (c : ℕ) * m), by
    have := chunkOf_mem hm x.2
    omega⟩
  left_inv i := by
    apply Fin.ext
    simp only [blockEmb_val]
    omega
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    have := chunkOf_mem hm x.2
    simp only [blockEmb_val]
    omega

/-- **Pinching along the `K` disjoint consecutive blocks of size `m` at offset `t`**
(Lemma 5 for the offset-`t` partition, prefix/suffix chunks dropped via `Ψ ≥ 0`):
`Σ_c tr Ψ(M_{B_c}) ≤ tr Ψ(M)` for PSD `M`. -/
theorem pinching_runs {r m K t : ℕ} (hm : 0 < m) (hKt : t + K * m ≤ r)
    {M : Matrix (Fin r) (Fin r) 𝕜} (hM : M.PosSemidef) :
    ∑ c : Fin K, ∑ i, Psi ((hM.submatrix (blockEmb hKt c)).1.eigenvalues i)
      ≤ ∑ j, Psi (hM.1.eigenvalues j) := by
  classical
  set φ : Fin r → Fin (K + 2) := chunkOf K t m hm with hφ
  set e : ((b : Fin (K + 2)) × {x : Fin r // φ x = b}) ≃ Fin r := Equiv.sigmaFiberEquiv φ
    with he
  have hM' : (M.submatrix ⇑e ⇑e).PosSemidef := hM.submatrix ⇑e
  have hpin := pinching_trPsi (γ := fun b : Fin (K + 2) => {x : Fin r // φ x = b}) hM'
  have hcard : Fintype.card ((b : Fin (K + 2)) × {x : Fin r // φ x = b}) = r := by
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hglob : ∑ j, Psi (hM'.1.eigenvalues j) = ∑ j, Psi (hM.1.eigenvalues j) := by
    have h2 := sum_g_eigenvalues_submatrix_equiv e hM (gc 2) (gc_zero (by norm_num))
    rw [sum_Psi_eq, sum_Psi_eq, hcard, Fintype.card_fin, h2]
  have hmain : ∀ c : Fin K,
      ∑ i, Psi ((hM.submatrix (blockEmb hKt c)).1.eigenvalues i)
        = ∑ i, Psi ((hM'.submatrix
            (Sigma.mk (⟨1 + (c : ℕ), by have := c.isLt; omega⟩ : Fin (K + 2)))).1.eigenvalues i)
      := by
    intro c
    set b : Fin (K + 2) := ⟨1 + (c : ℕ), by have := c.isLt; omega⟩ with hb
    set f := fiberEquiv hm hKt c with hf
    have hsub : (M.submatrix ⇑e ⇑e).submatrix (Sigma.mk b) (Sigma.mk b)
        = M.submatrix (fun x : {x : Fin r // φ x = b} => (x : Fin r))
            (fun x : {x : Fin r // φ x = b} => (x : Fin r)) := by
      rw [Matrix.submatrix_submatrix]
      rfl
    have hA : (M.submatrix (fun x : {x : Fin r // φ x = b} => (x : Fin r))
        (fun x : {x : Fin r // φ x = b} => (x : Fin r))).PosSemidef :=
      hM.submatrix _
    have hAf : (M.submatrix (fun x : {x : Fin r // φ x = b} => (x : Fin r))
          (fun x : {x : Fin r // φ x = b} => (x : Fin r))).submatrix ⇑f ⇑f
        = M.submatrix (blockEmb hKt c) (blockEmb hKt c) := by
      rw [Matrix.submatrix_submatrix]
      rfl
    have hcardf : Fintype.card {x : Fin r // φ x = b} = m := by
      rw [← Fintype.card_congr f, Fintype.card_fin]
    have h3 := sum_g_eigenvalues_submatrix_equiv f hA (gc 2) (gc_zero (by norm_num))
    have h4 : ∑ i, gc 2 ((hA.submatrix ⇑f).1.eigenvalues i)
        = ∑ i, gc 2 ((hM.submatrix (blockEmb hKt c)).1.eigenvalues i) :=
      sum_g_eigenvalues_congr hAf _ _ _
    have h5 : ∑ i, gc 2 ((hM'.submatrix (Sigma.mk b)).1.eigenvalues i)
        = ∑ i, gc 2 (hA.1.eigenvalues i) :=
      sum_g_eigenvalues_congr hsub _ _ _
    rw [sum_Psi_eq, sum_Psi_eq, hcardf, Fintype.card_fin, ← h4, h3, ← h5]
  have hsel : ∑ c : Fin K,
      ∑ i, Psi ((hM'.submatrix
          (Sigma.mk (⟨1 + (c : ℕ), by have := c.isLt; omega⟩ : Fin (K + 2)))).1.eigenvalues i)
      ≤ ∑ b : Fin (K + 2), ∑ i, Psi ((hM'.submatrix (Sigma.mk b)).1.eigenvalues i) := by
    set F : Fin (K + 2) → ℝ := fun b => ∑ i, Psi ((hM'.submatrix (Sigma.mk b)).1.eigenvalues i)
      with hF
    have hFnn : ∀ b, 0 ≤ F b := fun b => Finset.sum_nonneg fun i _ => Psi_nonneg _
    have hinj : Set.InjOn (fun c : Fin K => (⟨1 + (c : ℕ), by have := c.isLt; omega⟩ : Fin (K + 2)))
        (Finset.univ : Finset (Fin K)) := by
      intro c1 _ c2 _ h
      have := congrArg Fin.val h
      simp only at this
      exact Fin.ext (by omega)
    calc ∑ c : Fin K, F ⟨1 + (c : ℕ), by have := c.isLt; omega⟩
        = ∑ b ∈ (Finset.univ : Finset (Fin K)).image
            (fun c : Fin K => (⟨1 + (c : ℕ), by have := c.isLt; omega⟩ : Fin (K + 2))), F b := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ b : Fin (K + 2), F b :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hFnn b
  have hstep1 : ∑ c : Fin K, ∑ i, Psi ((hM.submatrix (blockEmb hKt c)).1.eigenvalues i)
      = ∑ c : Fin K, ∑ i, Psi ((hM'.submatrix
          (Sigma.mk (⟨1 + (c : ℕ), by have := c.isLt; omega⟩ : Fin (K + 2)))).1.eigenvalues i) :=
    Finset.sum_congr rfl fun c _ => hmain c
  exact hstep1.trans_le (le_trans hsel (le_trans hpin hglob.le))

end Pinching

/-! ## Layer 1.  One block: window summation + block defect (Lemmas 4.2 + 4.3) -/

/-- **One block**: on a block of `m` consecutive retained points (embedded by `e`,
`(e i : ℕ) = o + i`), the certified 7-point inequality plus the near-pair Gram control
give `tr Ψ(G_B) ≥ β(m−6) − span_B/500 − 2m²ε`. -/
theorem block_lower {r m : ℕ} (hm : 7 ≤ m)
    {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x) {β : ℝ}
    (hβ : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → β ≤ F6 w g)
    (hβ1 : β * ((m : ℝ) - 6) ≤ 1)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    {y : Fin r → ℝ} (hy : StrictMono y)
    {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosSemidef)
    (hGw : ∀ i j : Fin r, (i : ℕ) < (j : ℕ) → (j : ℕ) < (i : ℕ) + m →
      w (y j - y i) ≤ ‖G i j‖ ^ 2 + ε)
    {e : Fin m → Fin r} {o : ℕ} (he : ∀ i : Fin m, (e i : ℕ) = o + (i : ℕ)) :
    β * ((m : ℝ) - 6) - (1 / 500) * (y (e ⟨m - 1, by omega⟩) - y (e ⟨0, by omega⟩))
        - 2 * (m : ℝ) ^ 2 * ε
      ≤ ∑ i, Psi ((hG.submatrix e).1.eigenvalues i) := by
  have hm0 : 0 < m := by omega
  set yB : Fin m → ℝ := fun i => y (e i) with hyB
  have hyBmono : StrictMono yB := by
    intro i j hij
    refine hy ?_
    rw [Fin.lt_def, he i, he j]
    rw [Fin.lt_def] at hij
    omega
  have hwin := window_summation hm hw hβ hyBmono
  have hpair : ∀ j : Fin m, ∀ i ∈ Finset.Iio j,
      w (yB j - yB i) ≤ ‖(G.submatrix e e) i j‖ ^ 2 + ε := by
    intro j i hi
    rw [Finset.mem_Iio, Fin.lt_def] at hi
    have h1 : (e i : ℕ) < (e j : ℕ) := by rw [he i, he j]; omega
    have h2 : (e j : ℕ) < (e i : ℕ) + m := by
      rw [he i, he j]
      have := j.isLt
      omega
    exact hGw (e i) (e j) h1 h2
  have hcnt : ∑ j : Fin m, ∑ _i ∈ Finset.Iio j, ε ≤ (m : ℝ) ^ 2 * ε := by
    have hone : ∀ j : Fin m, ∑ _i ∈ Finset.Iio j, ε ≤ (m : ℝ) * ε := by
      intro j
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Iio j).card : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast le_trans (Finset.card_le_univ _) (le_of_eq (Finset.card_fin m))
      exact mul_le_mul_of_nonneg_right hcard hε0
    calc ∑ j : Fin m, ∑ _i ∈ Finset.Iio j, ε
        ≤ ∑ _j : Fin m, (m : ℝ) * ε := Finset.sum_le_sum fun j _ => hone j
      _ = (m : ℝ) * ((m : ℝ) * ε) := by
          simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
      _ = (m : ℝ) ^ 2 * ε := by ring
  have hswap : ∑ j : Fin m, ∑ i ∈ Finset.Iio j, ‖(G.submatrix e e) i j‖ ^ 2
      = ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, ‖(G.submatrix e e) i j‖ ^ 2 :=
    sum_Iio_swap (fun j i => ‖(G.submatrix e e) i j‖ ^ 2)
  have hEm : Em w yB ≤ 2 * (∑ i, ∑ j ∈ Finset.Ioi i, ‖(G.submatrix e e) i j‖ ^ 2)
      + 2 * (m : ℝ) ^ 2 * ε := by
    have hstep : ∑ j : Fin m, ∑ i ∈ Finset.Iio j, w (yB j - yB i)
        ≤ ∑ j : Fin m, ∑ i ∈ Finset.Iio j, (‖(G.submatrix e e) i j‖ ^ 2 + ε) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i hi => hpair j i hi
    have hdist : ∑ j : Fin m, ∑ i ∈ Finset.Iio j, (‖(G.submatrix e e) i j‖ ^ 2 + ε)
        = (∑ j : Fin m, ∑ i ∈ Finset.Iio j, ‖(G.submatrix e e) i j‖ ^ 2)
          + ∑ j : Fin m, ∑ _i ∈ Finset.Iio j, ε := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_add_distrib
    unfold Em
    rw [hswap] at hdist
    nlinarith [hstep, hcnt, hdist]
  have hbd := block_defect (hG.submatrix e)
  have hspan0 : 0 ≤ yB ⟨m - 1, by omega⟩ - yB ⟨0, by omega⟩ := by
    refine sub_nonneg.mpr (hyBmono.monotone ?_)
    rw [Fin.le_def]
    simp
  have ht2 : β * ((m : ℝ) - 6)
        - (1 / 500) * (yB ⟨m - 1, by omega⟩ - yB ⟨0, by omega⟩) - 2 * (m : ℝ) ^ 2 * ε
      ≤ 2 * (∑ i, ∑ j ∈ Finset.Ioi i, ‖(G.submatrix e e) i j‖ ^ 2) := by
    have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [hwin, hEm]
  have ht1 : β * ((m : ℝ) - 6)
        - (1 / 500) * (yB ⟨m - 1, by omega⟩ - yB ⟨0, by omega⟩) - 2 * (m : ℝ) ^ 2 * ε
      ≤ 1 := by
    have h2m : 0 ≤ 2 * (m : ℝ) ^ 2 * ε := by positivity
    linarith
  calc β * ((m : ℝ) - 6)
        - (1 / 500) * (y (e ⟨m - 1, by omega⟩) - y (e ⟨0, by omega⟩)) - 2 * (m : ℝ) ^ 2 * ε
      = β * ((m : ℝ) - 6)
        - (1 / 500) * (yB ⟨m - 1, by omega⟩ - yB ⟨0, by omega⟩) - 2 * (m : ℝ) ^ 2 * ε := rfl
    _ ≤ min 1 (2 * (∑ i, ∑ j ∈ Finset.Ioi i, ‖(G.submatrix e e) i j‖ ^ 2)) := le_min ht1 ht2
    _ ≤ ∑ i, Psi ((hG.submatrix e).1.eigenvalues i) := hbd

/-! ## Layer 1.  The aggregated defect bound (4.6) -/

/-- **The aggregated defect bound** (Lemmas 4.2 + 4.3 + 5, averaged over the `m` block
offsets): for `A₀ := β(m−6)`,
`m·tr Ψ(G) ≥ A₀·r − (m−1)·A₀ − r·(2m²ε) − ((m−1)/500)·(y_{r−1} − y_0)`. -/
theorem defect_lower {r m : ℕ} (hm : 7 ≤ m) (hr : 0 < r)
    {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x) {β : ℝ}
    (hβ : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → β ≤ F6 w g)
    (hβ1 : β * ((m : ℝ) - 6) ≤ 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : 2 * (m : ℝ) ^ 2 * ε ≤ β * ((m : ℝ) - 6))
    {y : Fin r → ℝ} (hy : StrictMono y)
    {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosSemidef)
    (hGw : ∀ i j : Fin r, (i : ℕ) < (j : ℕ) → (j : ℕ) < (i : ℕ) + m →
      w (y j - y i) ≤ ‖G i j‖ ^ 2 + ε) :
    β * ((m : ℝ) - 6) * (r : ℝ) - ((m : ℝ) - 1) * (β * ((m : ℝ) - 6))
        - (r : ℝ) * (2 * (m : ℝ) ^ 2 * ε)
        - (((m : ℝ) - 1) / 500) * (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩)
      ≤ (m : ℝ) * ∑ j, Psi (hG.1.eigenvalues j) := by
  have hm0 : 0 < m := by omega
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hE0 : 0 ≤ 2 * (m : ℝ) ^ 2 * ε := by positivity
  have hA0 : 0 ≤ β * ((m : ℝ) - 6) := le_trans hE0 hε1
  have hspan0 : 0 ≤ y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩ := by
    refine sub_nonneg.mpr (hy.monotone ?_)
    rw [Fin.le_def]
    simp
  have hΔ0 : 0 ≤ ∑ j, Psi (hG.1.eigenvalues j) :=
    Finset.sum_nonneg fun j _ => Psi_nonneg _
  by_cases hmr : r < m
  · have h1 : (r : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hmr
    have h2 : β * ((m : ℝ) - 6) * ((r : ℝ) - ((m : ℝ) - 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hA0 (by linarith)
    have h3 : 0 ≤ (r : ℝ) * (2 * (m : ℝ) ^ 2 * ε) := by positivity
    have h4 : 0 ≤ (((m : ℝ) - 1) / 500) * (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩) :=
      mul_nonneg (by linarith) hspan0
    have h5 : 0 ≤ (m : ℝ) * ∑ j, Psi (hG.1.eigenvalues j) :=
      mul_nonneg (by linarith) hΔ0
    nlinarith [h2]
  push_neg at hmr
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
  set A₀ : ℝ := β * ((m : ℝ) - 6) with hA₀def
  set E : ℝ := 2 * (m : ℝ) ^ 2 * ε with hEdef
  set Δ : ℝ := ∑ j, Psi (hG.1.eigenvalues j) with hΔdef
  have hoff : ∀ t ∈ Finset.range m,
      ((r - t) / m : ℕ) * (A₀ - E)
        - (1 / 500) * ∑ c ∈ Finset.range ((r - t) / m),
            (Y (t + c * m + (m - 1)) - Y (t + c * m))
      ≤ Δ := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hKt : t + ((r - t) / m) * m ≤ r := by
      have h1 : (r - t) / m * m ≤ r - t := Nat.div_mul_le_self _ _
      omega
    set K : ℕ := (r - t) / m with hKdef
    have hpin := pinching_runs hm0 hKt hG
    have hblocks : ∀ c : Fin K,
        A₀ - (1 / 500) * (Y (t + (c : ℕ) * m + (m - 1)) - Y (t + (c : ℕ) * m)) - E
          ≤ ∑ i, Psi ((hG.submatrix (blockEmb hKt c)).1.eigenvalues i) := by
      intro c
      have hbl := block_lower hm hw hβ hβ1 hε0 hy hG hGw
        (e := blockEmb hKt c) (o := t + (c : ℕ) * m)
        (fun i => blockEmb_val hKt c i)
      have he1 : y (blockEmb hKt c ⟨m - 1, by omega⟩) = Y (t + (c : ℕ) * m + (m - 1)) :=
        (hYval (blockEmb hKt c ⟨m - 1, by omega⟩)).symm
      have he0 : y (blockEmb hKt c ⟨0, by omega⟩) = Y (t + (c : ℕ) * m) := by
        have h := (hYval (blockEmb hKt c ⟨0, by omega⟩)).symm
        rw [h]
        congr 1
      rw [he1, he0] at hbl
      exact hbl
    have hsum := Finset.sum_le_sum fun c (_ : c ∈ (Finset.univ : Finset (Fin K))) => hblocks c
    have hLHS : ∑ c : Fin K,
        (A₀ - (1 / 500) * (Y (t + (c : ℕ) * m + (m - 1)) - Y (t + (c : ℕ) * m)) - E)
        = (K : ℝ) * (A₀ - E)
          - (1 / 500) * ∑ c ∈ Finset.range K, (Y (t + c * m + (m - 1)) - Y (t + c * m)) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun c => A₀ - (1 / 500) * (Y (t + c * m + (m - 1)) - Y (t + c * m)) - E) K]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hLHS] at hsum
    exact le_trans hsum hpin
  have hsum2 := Finset.sum_le_sum hoff
  have hRHS : ∑ _t ∈ Finset.range m, Δ = (m : ℝ) * Δ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hLHS2 : ∑ t ∈ Finset.range m,
      (((r - t) / m : ℕ) * (A₀ - E)
        - (1 / 500) * ∑ c ∈ Finset.range ((r - t) / m),
            (Y (t + c * m + (m - 1)) - Y (t + c * m)))
      = (∑ t ∈ Finset.range m, ((r - t) / m : ℕ) : ℝ) * (A₀ - E)
        - (1 / 500) * ∑ t ∈ Finset.range m, ∑ c ∈ Finset.range ((r - t) / m),
            (Y (t + c * m + (m - 1)) - Y (t + c * m)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hRHS, hLHS2] at hsum2
  have hks : ((r : ℝ) + 1 - (m : ℝ)) ≤ (∑ t ∈ Finset.range m, ((r - t) / m : ℕ) : ℝ) := by
    have h := sum_blocks_ge hm0 hmr
    have hcast : ((r + 1 - m : ℕ) : ℝ) = (r : ℝ) + 1 - (m : ℝ) := by
      have : m ≤ r + 1 := by omega
      push_cast [Nat.cast_sub this]
      ring
    calc (r : ℝ) + 1 - (m : ℝ) = ((r + 1 - m : ℕ) : ℝ) := hcast.symm
      _ ≤ ((∑ t ∈ Finset.range m, (r - t) / m : ℕ) : ℝ) := by exact_mod_cast h
      _ = (∑ t ∈ Finset.range m, ((r - t) / m : ℕ) : ℝ) := by rw [Nat.cast_sum]
  have hsp := sum_spans_le (show 1 ≤ m by omega) (r := r) hY
  have hYr : Y (r - 1) = y ⟨r - 1, by omega⟩ := hYval ⟨r - 1, by omega⟩
  have hY0 : Y 0 = y ⟨0, hr⟩ := hYval ⟨0, hr⟩
  rw [hYr, hY0] at hsp
  have hAE : 0 ≤ A₀ - E := by rw [hA₀def, hEdef]; linarith
  have hprod : ((r : ℝ) + 1 - (m : ℝ)) * (A₀ - E)
      ≤ (∑ t ∈ Finset.range m, ((r - t) / m : ℕ) : ℝ) * (A₀ - E) :=
    mul_le_mul_of_nonneg_right hks hAE
  have hexp : ((r : ℝ) + 1 - (m : ℝ)) * (A₀ - E)
      = (r : ℝ) * A₀ - ((m : ℝ) - 1) * A₀ - (r : ℝ) * E + ((m : ℝ) - 1) * E := by
    ring
  have hEnn : 0 ≤ ((m : ℝ) - 1) * E := mul_nonneg (by linarith) hE0
  have hspmul : (1 / 500) * (∑ t ∈ Finset.range m, ∑ c ∈ Finset.range ((r - t) / m),
        (Y (t + c * m + (m - 1)) - Y (t + c * m)))
      ≤ (1 / 500) * (((m : ℝ) - 1) * (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩)) := by
    have h500 : (0 : ℝ) ≤ 1 / 500 := by norm_num
    exact mul_le_mul_of_nonneg_left hsp h500
  have hfin : (r : ℝ) * A₀ - ((m : ℝ) - 1) * A₀ - (r : ℝ) * E
      - (((m : ℝ) - 1) / 500) * (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩)
      ≤ (m : ℝ) * Δ := by
    have e1 : (((m : ℝ) - 1) / 500) * (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩)
        = (1 / 500) * (((m : ℝ) - 1) * (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩)) := by ring
    rw [e1]
    linarith [hsum2, hprod, hspmul]
  linarith [hfin]

/-! ## Layer 1.  The stability-enhanced seam and the counting theorems -/

/-- **The stability-enhanced seam** (the (2.2)-analogue at the matrix level): from the
stability rank–trace inequality (Lemma 2.1, imported) and the configuration count
`3r + 4b ≤ S + 2N`, every count `S` obeys
`S ≥ 4·tr(VVᴴ+Q) − ‖VVᴴ+Q‖_F² − 2N + tr Ψ(VᴴV)`. -/
theorem stability_seam {d r : ℕ} {V : Matrix (Fin d) (Fin r) ℂ}
    (hV : ∀ j, colSq V j ≤ 1)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b)
    {S N : ℝ} (hcount : 3 * (r : ℝ) + 4 * (b : ℝ) ≤ S + 2 * N) :
    4 * rtrace (V * Vᴴ + Q) - frobSq (V * Vᴴ + Q) - 2 * N
        + ∑ j, Psi ((Matrix.posSemidef_conjTranspose_mul_self V).1.eigenvalues j) ≤ S := by
  have hM : (Vᴴ * V).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self V).1
  have h := Zeta23Ext.StabilityRankTrace.stability_rank_trace V hV hM hQ hb
  have hPsi : ∑ j, Psi (hM.eigenvalues j)
      = ∑ j, Zeta23Ext.StabilityRankTrace.Psi (hM.eigenvalues j) := rfl
  have hcard : (Fintype.card (Fin r) : ℝ) = (r : ℝ) := by rw [Fintype.card_fin]
  rw [show (Matrix.posSemidef_conjTranspose_mul_self V).1 = hM from rfl, hPsi]
  linarith [h]

/-- The seam + the second-moment bounds: `S ≥ (2−κ)N − (4R₁+R₂) + tr Ψ(VᴴV)`. -/
theorem stability_seam_moment {d r : ℕ} {V : Matrix (Fin d) (Fin r) ℂ}
    (hV : ∀ j, colSq V j ≤ 1)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b)
    {S N R₁ R₂ κ : ℝ} (hcount : 3 * (r : ℝ) + 4 * (b : ℝ) ≤ S + 2 * N)
    (htr : N - R₁ ≤ rtrace (V * Vᴴ + Q))
    (hfr : frobSq (V * Vᴴ + Q) ≤ κ * N + R₂) :
    (2 - κ) * N - (4 * R₁ + R₂)
        + ∑ j, Psi ((Matrix.posSemidef_conjTranspose_mul_self V).1.eigenvalues j) ≤ S := by
  have h := stability_seam hV hQ hb hcount
  linarith [h]

/-- **LAYER 1, main theorem: the abstract defect-enhanced counting inequality**
(paper (2.2) + (4.6)).  Given (i) the 7-point hypothesis for `w` at constant `β`,
(ii) the near-pair Gram control on `M = VᴴV` (the kernel-limit conclusion), (iii) the
stability rank–trace inequality (imported), and (iv) the block/pinching/averaging scheme
at block length `m`:

  `S ≥ (2−κ)·N + (β(m−6)/m)·S − ((m−1)/(500m))·N − (4R₁ + R₂ + 2mrε + β(m−6))`. -/
theorem stability_counting {d r m b : ℕ} (hm : 7 ≤ m) (hr : 0 < r)
    {V : Matrix (Fin d) (Fin r) ℂ} (hV : ∀ j, colSq V j ≤ 1)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) (hb : posIndex hQ ≤ b)
    {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    {β : ℝ} (hβ : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → β ≤ F6 w g)
    (hβ1 : β * ((m : ℝ) - 6) ≤ 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : 2 * (m : ℝ) ^ 2 * ε ≤ β * ((m : ℝ) - 6))
    {y : Fin r → ℝ} (hy : StrictMono y)
    (hGw : ∀ i j : Fin r, (i : ℕ) < (j : ℕ) → (j : ℕ) < (i : ℕ) + m →
      w (y j - y i) ≤ ‖(Vᴴ * V) i j‖ ^ 2 + ε)
    {S N R₁ R₂ κ : ℝ}
    (hcount : 3 * (r : ℝ) + 4 * (b : ℝ) ≤ S + 2 * N)
    (hrS : S ≤ (r : ℝ))
    (hspan : y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩ ≤ N)
    (htr : N - R₁ ≤ rtrace (V * Vᴴ + Q))
    (hfr : frobSq (V * Vᴴ + Q) ≤ κ * N + R₂) :
    (2 - κ) * N + (β * ((m : ℝ) - 6) / (m : ℝ)) * S - (((m : ℝ) - 1) / (500 * (m : ℝ))) * N
        - (4 * R₁ + R₂ + 2 * (m : ℝ) * (r : ℝ) * ε + β * ((m : ℝ) - 6)) ≤ S := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hG : (Vᴴ * V).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self V
  set Δ : ℝ := ∑ j, Psi (hG.1.eigenvalues j) with hΔdef
  have hseam : (2 - κ) * N - (4 * R₁ + R₂) + Δ ≤ S := by
    have h := stability_seam_moment hV hQ hb hcount htr hfr
    exact h
  have hdef := defect_lower hm hr hw hβ hβ1 hε0 hε1 hy hG hGw
  set A₀ : ℝ := β * ((m : ℝ) - 6) with hA₀def
  have hE0 : 0 ≤ 2 * (m : ℝ) ^ 2 * ε := by positivity
  have hA0 : 0 ≤ A₀ := le_trans hE0 hε1
  have hstep : A₀ * S - ((m : ℝ) - 1) * A₀ - (r : ℝ) * (2 * (m : ℝ) ^ 2 * ε)
      - (((m : ℝ) - 1) / 500) * N ≤ (m : ℝ) * Δ := by
    have h1 : A₀ * S ≤ A₀ * (r : ℝ) := mul_le_mul_of_nonneg_left hrS hA0
    have h2 : (((m : ℝ) - 1) / 500) * (y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩)
        ≤ (((m : ℝ) - 1) / 500) * N := by
      have hc : (0 : ℝ) ≤ ((m : ℝ) - 1) / 500 := by
        have h7 : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      exact mul_le_mul_of_nonneg_left hspan hc
    nlinarith [hdef]
  have hΔge : (A₀ / (m : ℝ)) * S - (((m : ℝ) - 1) / (m : ℝ)) * A₀
      - 2 * (m : ℝ) * (r : ℝ) * ε - (((m : ℝ) - 1) / (500 * (m : ℝ))) * N ≤ Δ := by
    rw [show (A₀ / (m : ℝ)) * S - (((m : ℝ) - 1) / (m : ℝ)) * A₀
        - 2 * (m : ℝ) * (r : ℝ) * ε - (((m : ℝ) - 1) / (500 * (m : ℝ))) * N
      = (A₀ * S - ((m : ℝ) - 1) * A₀ - (r : ℝ) * (2 * (m : ℝ) ^ 2 * ε)
          - (((m : ℝ) - 1) / 500) * N) / (m : ℝ) from by field_simp; try ring]
    rw [div_le_iff₀ hm0]
    linarith [hstep]
  have hfrac : (((m : ℝ) - 1) / (m : ℝ)) * A₀ ≤ A₀ := by
    have h1 : ((m : ℝ) - 1) / (m : ℝ) ≤ 1 := by
      rw [div_le_one hm0]
      linarith
    nlinarith [hA0]
  linarith [hseam, hΔge, hfrac]

/-- **LAYER 1, endgame (ratio) form** ((4.6) → (4.7)):
`S ≥ ((2 − κ − (m−1)/(500m)) / (1 − β(m−6)/m))·N − errors/(1 − β(m−6)/m)`. -/
theorem stability_counting_ratio {d r m b : ℕ} (hm : 7 ≤ m) (hr : 0 < r)
    {V : Matrix (Fin d) (Fin r) ℂ} (hV : ∀ j, colSq V j ≤ 1)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) (hb : posIndex hQ ≤ b)
    {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    {β : ℝ} (hβ : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → β ≤ F6 w g)
    (hβ1 : β * ((m : ℝ) - 6) ≤ 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : 2 * (m : ℝ) ^ 2 * ε ≤ β * ((m : ℝ) - 6))
    {y : Fin r → ℝ} (hy : StrictMono y)
    (hGw : ∀ i j : Fin r, (i : ℕ) < (j : ℕ) → (j : ℕ) < (i : ℕ) + m →
      w (y j - y i) ≤ ‖(Vᴴ * V) i j‖ ^ 2 + ε)
    {S N R₁ R₂ κ : ℝ}
    (hcount : 3 * (r : ℝ) + 4 * (b : ℝ) ≤ S + 2 * N)
    (hrS : S ≤ (r : ℝ))
    (hspan : y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩ ≤ N)
    (htr : N - R₁ ≤ rtrace (V * Vᴴ + Q))
    (hfr : frobSq (V * Vᴴ + Q) ≤ κ * N + R₂) :
    ((2 - κ - ((m : ℝ) - 1) / (500 * (m : ℝ))) / (1 - β * ((m : ℝ) - 6) / (m : ℝ))) * N
        - (4 * R₁ + R₂ + 2 * (m : ℝ) * (r : ℝ) * ε + β * ((m : ℝ) - 6))
            / (1 - β * ((m : ℝ) - 6) / (m : ℝ)) ≤ S := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have h := stability_counting hm hr hV hQ hb hw hβ hβ1 hε0 hε1 hy hGw
    hcount hrS hspan htr hfr
  set a : ℝ := β * ((m : ℝ) - 6) / (m : ℝ) with hadef
  set bb : ℝ := ((m : ℝ) - 1) / (500 * (m : ℝ)) with hbbdef
  set Err : ℝ := 4 * R₁ + R₂ + 2 * (m : ℝ) * (r : ℝ) * ε + β * ((m : ℝ) - 6) with hErrdef
  have ha1 : a ≤ 1 / (m : ℝ) := by
    rw [hadef]
    gcongr
  have ha2 : 1 / (m : ℝ) ≤ 1 / 7 := by
    rw [div_le_div_iff₀ hm0 (by norm_num : (0:ℝ) < 7)]
    linarith
  have h1a : 0 < 1 - a := by linarith
  have hstep : (2 - κ - bb) * N - Err ≤ (1 - a) * S := by linarith [h]
  have hid : ((2 - κ - bb) / (1 - a)) * N - Err / (1 - a)
      = ((2 - κ - bb) * N - Err) / (1 - a) := by ring
  rw [hid, div_le_iff₀ h1a]
  linarith [hstep]

/-! ## Layer 1.  The specialized corollary at m = 267, β = betaCert = 191/50000 -/

/-- **LAYER 1, certified corollary** at `m = 267`, `β = betaCert = 191/50000`
(`A₀ = β·261 = 49851/50000`, `a = A₀/267 = 16617/4450000`, `b = 266/133500 = 133/66750`):

  `S ≥ ((2 − κ − 133/66750) / (1 − 16617/4450000))·N − errors`. -/
theorem stability_counting_certified {d r b : ℕ} (hr : 0 < r)
    {V : Matrix (Fin d) (Fin r) ℂ} (hV : ∀ j, colSq V j ≤ 1)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) (hb : posIndex hQ ≤ b)
    {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hβ : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → Bridge.betaCert ≤ F6 w g)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 300000)
    {y : Fin r → ℝ} (hy : StrictMono y)
    (hGw : ∀ i j : Fin r, (i : ℕ) < (j : ℕ) → (j : ℕ) < (i : ℕ) + 267 →
      w (y j - y i) ≤ ‖(Vᴴ * V) i j‖ ^ 2 + ε)
    {S N R₁ R₂ κ : ℝ}
    (hcount : 3 * (r : ℝ) + 4 * (b : ℝ) ≤ S + 2 * N)
    (hrS : S ≤ (r : ℝ))
    (hspan : y ⟨r - 1, by omega⟩ - y ⟨0, hr⟩ ≤ N)
    (htr : N - R₁ ≤ rtrace (V * Vᴴ + Q))
    (hfr : frobSq (V * Vᴴ + Q) ≤ κ * N + R₂) :
    ((2 - κ - 133 / 66750) / (1 - 16617 / 4450000)) * N
        - (4 * R₁ + R₂ + 534 * (r : ℝ) * ε + 49851 / 50000) / (1 - 16617 / 4450000) ≤ S := by
  have hβ1 : Bridge.betaCert * (((267 : ℕ) : ℝ) - 6) ≤ 1 := by
    rw [Bridge.betaCert_eq]
    norm_num
  have hε1' : 2 * ((267 : ℕ) : ℝ) ^ 2 * ε ≤ Bridge.betaCert * (((267 : ℕ) : ℝ) - 6) := by
    rw [Bridge.betaCert_eq]
    norm_num
    linarith
  have h := stability_counting_ratio (m := 267) (by norm_num) hr hV hQ hb hw hβ hβ1 hε0 hε1'
    hy hGw hcount hrS hspan htr hfr
  have e1 : (((267 : ℕ) : ℝ) - 1) / (500 * ((267 : ℕ) : ℝ)) = 133 / 66750 := by norm_num
  have e2 : Bridge.betaCert * (((267 : ℕ) : ℝ) - 6) / ((267 : ℕ) : ℝ) = 16617 / 4450000 := by
    rw [Bridge.betaCert_eq]
    norm_num
  have e3 : Bridge.betaCert * (((267 : ℕ) : ℝ) - 6) = 49851 / 50000 := by
    rw [Bridge.betaCert_eq]
    norm_num
  have e4 : 2 * ((267 : ℕ) : ℝ) * (r : ℝ) * ε = 534 * (r : ℝ) * ε := by norm_num
  rw [e1, e2, e4, e3] at h
  exact h

end Stability
end Zeta23Ext

end
