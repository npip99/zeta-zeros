import Zeta23Ext.TranscendentalBounds

noncomputable section
open Set

namespace Zeta23Ext.RationalTrigCell

/-- Compact rational witness for a sine cell after subtracting `k*pi`. -/
structure Witness where
  k : ℤ
  center : ℚ
  radius : ℚ
  upper : ℚ
  err : ℚ

def check (w : Witness) : Bool :=
  decide (0 < w.upper ∧ 0 ≤ w.center ∧ w.center ≤ w.upper ∧
    0 ≤ w.radius ∧ w.radius + w.center ^ 8 / 5040 ≤ w.err)

lemma check_sound {w : Witness} (h : check w = true) :
    0 < w.upper ∧ 0 ≤ w.center ∧ w.center ≤ w.upper ∧
      0 ≤ w.radius ∧ w.radius + w.center ^ 8 / 5040 ≤ w.err := by
  simpa [check] using of_decide_eq_true h

/-- A checked rational row bounds sine at every real argument whose
`k*pi`-reduction lies in its rational cell. -/
theorem sin_sound {w : Witness} (hw : check w = true) {x : ℝ}
    (hcell : |(x - (w.k : ℝ) * Real.pi) - (w.center : ℝ)| ≤ (w.radius : ℝ)) :
    |((-1 : ℝ) ^ w.k) * Real.sin x -
        TranscendentalBounds.sinTaylor7 (w.center : ℝ)| ≤ (w.err : ℝ) := by
  obtain ⟨hu, hc0, hcu, hr0, herr⟩ := check_sound hw
  have ht := TranscendentalBounds.abs_sin_sub_taylor7_center_le
    (upper := (w.upper : ℝ)) (c := (w.center : ℝ))
    (x := x - (w.k : ℝ) * Real.pi) (by exact_mod_cast hu)
    (by constructor
        · exact_mod_cast hc0
        · exact_mod_cast hcu) (by exact_mod_cast hcell)
  rw [Real.sin_sub_int_mul_pi] at ht
  have herrR : (w.radius : ℝ) + (w.center : ℝ) ^ 8 / 5040 ≤ (w.err : ℝ) := by
    exact_mod_cast herr
  exact ht.trans herrR

theorem sin_mem_interval {w : Witness} (hw : check w = true) {x : ℝ}
    (hcell : |(x - (w.k : ℝ) * Real.pi) - (w.center : ℝ)| ≤ (w.radius : ℝ)) :
    (w.center : ℝ) |> TranscendentalBounds.sinTaylor7 |>
        (fun approximation => approximation - (w.err : ℝ) ≤
          ((-1 : ℝ) ^ w.k) * Real.sin x ∧
          ((-1 : ℝ) ^ w.k) * Real.sin x ≤ approximation + (w.err : ℝ)) := by
  have h := sin_sound hw hcell
  obtain ⟨hu, hl⟩ := abs_sub_le_iff.mp h
  constructor <;> linarith

/-! ## Cosine cells -/

/-- The same range-reduction data with the order-eight cosine remainder. -/
def cosCheck (w : Witness) : Bool :=
  decide (0 < w.upper ∧ 0 ≤ w.center ∧ w.center ≤ w.upper ∧
    0 ≤ w.radius ∧ w.radius + w.center ^ 9 / 40320 ≤ w.err)

lemma cosCheck_sound {w : Witness} (h : cosCheck w = true) :
    0 < w.upper ∧ 0 ≤ w.center ∧ w.center ≤ w.upper ∧
      0 ≤ w.radius ∧ w.radius + w.center ^ 9 / 40320 ≤ w.err := by
  simpa [cosCheck] using of_decide_eq_true h

/-- Accepted rational data bounds cosine on a whole range-reduced cell. -/
theorem cos_sound {w : Witness} (hw : cosCheck w = true) {x : ℝ}
    (hcell : |(x - (w.k : ℝ) * Real.pi) - (w.center : ℝ)| ≤ (w.radius : ℝ)) :
    |((-1 : ℝ) ^ w.k) * Real.cos x -
        TranscendentalBounds.cosTaylor8 (w.center : ℝ)| ≤ (w.err : ℝ) := by
  obtain ⟨hu, hc0, hcu, hr0, herr⟩ := cosCheck_sound hw
  have ht := TranscendentalBounds.abs_cos_sub_taylor8_center_le
    (upper := (w.upper : ℝ)) (c := (w.center : ℝ))
    (x := x - (w.k : ℝ) * Real.pi) (by exact_mod_cast hu)
    (by constructor
        · exact_mod_cast hc0
        · exact_mod_cast hcu) (by exact_mod_cast hcell)
  rw [Real.cos_sub_int_mul_pi] at ht
  have herrR : (w.radius : ℝ) + (w.center : ℝ) ^ 9 / 40320 ≤ (w.err : ℝ) := by
    exact_mod_cast herr
  exact ht.trans herrR

theorem cos_mem_interval {w : Witness} (hw : cosCheck w = true) {x : ℝ}
    (hcell : |(x - (w.k : ℝ) * Real.pi) - (w.center : ℝ)| ≤ (w.radius : ℝ)) :
    (w.center : ℝ) |> TranscendentalBounds.cosTaylor8 |>
        (fun approximation => approximation - (w.err : ℝ) ≤
          ((-1 : ℝ) ^ w.k) * Real.cos x ∧
          ((-1 : ℝ) ^ w.k) * Real.cos x ≤ approximation + (w.err : ℝ)) := by
  have h := cos_sound hw hcell
  obtain ⟨hu, hl⟩ := abs_sub_le_iff.mp h
  constructor <;> linarith

/-! ## Combining certified terms -/

/-- Independent absolute-error rows combine with the exact coefficient signs.
This is the arithmetic layer used by generated seven-term window rows. -/
theorem weighted_sum_le {n : ℕ} (coefficient value approximation error : Fin n → ℝ)
    (herror : ∀ i, |value i - approximation i| ≤ error i) :
    ∑ i, coefficient i * value i ≤
      ∑ i, coefficient i * approximation i +
        ∑ i, |coefficient i| * error i := by
  have hterm : ∀ i, coefficient i * value i ≤
      coefficient i * approximation i + |coefficient i| * error i := by
    intro i
    have hdiff : value i - approximation i ≤ error i :=
      (le_abs_self _).trans (herror i)
    have hdiff' : -(error i) ≤ value i - approximation i :=
      (neg_le_of_abs_le (herror i))
    rcases le_total 0 (coefficient i) with hc | hc
    · rw [abs_of_nonneg hc]
      nlinarith
    · rw [abs_of_nonpos hc]
      nlinarith
  calc
    ∑ i, coefficient i * value i ≤
        ∑ i, (coefficient i * approximation i + |coefficient i| * error i) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = ∑ i, coefficient i * approximation i +
        ∑ i, |coefficient i| * error i := by rw [Finset.sum_add_distrib]

def regression : Witness := ⟨0, 1 / 2, 1 / 100, 1, 1 / 50⟩

example : check regression = true := by norm_num [check, regression]

example : cosCheck regression = true := by norm_num [cosCheck, regression]

end Zeta23Ext.RationalTrigCell
end
