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

def regression : Witness := ⟨0, 1 / 2, 1 / 100, 1, 1 / 50⟩

example : check regression = true := by norm_num [check, regression]

end Zeta23Ext.RationalTrigCell
end
