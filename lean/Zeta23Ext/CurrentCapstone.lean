/-
Conditional capstone for the current weighted-window result.

The genuinely current inputs are exposed rather than silently identified with
the old `Zeta23Ext.Final` theorem.  In particular, a caller must supply:

* the stability seam with constant `Hcert = 672457/10^6`; and
* the weighted block-defect inequality with reward `R = 2*sqrt(A)-1` and
  pressure loss `eta * (3/1150) * 249/250`.

The local weighted seven-point certificate and the analytic window bridge are
therefore outside the trust boundary of this file.  Once those two inequalities
are supplied, all rearrangement and final arithmetic below are kernel-checked.
-/
import Zeta23Ext.CurrentConstants

noncomputable section

open Filter

namespace Zeta23Ext.Current

/-- The two abstract inequalities consumed by the current-result endgame.

`defect` denotes `tr Ψ(M)`.  `stabilityError` is the `o(N)` loss in the
imported stability seam.  `blockError` collects the uniform Gram error,
endpoint loss, span error, and the `O(1)` losses from shifted-block
averaging. -/
structure WeightedBlockDefectData
    (S N defect stabilityError blockError : ℝ) : Prop where
  N_nonneg : 0 ≤ N
  stabilitySeam : Hcert * N + defect - stabilityError ≤ S
  weightedBlockDefect :
    R / (m : ℝ) * S -
        eta * pressureCap * (((m : ℝ) - 1) / (m : ℝ)) * N - blockError ≤ defect

/-- The stability seam and weighted block-defect input combine to the exact
pre-division inequality printed in the paper. -/
theorem WeightedBlockDefectData.combined
    {S N defect stabilityError blockError : ℝ}
    (h : WeightedBlockDefectData S N defect stabilityError blockError) :
    Hcert * N + R / (m : ℝ) * S -
        eta * pressureCap * (((m : ℝ) - 1) / (m : ℝ)) * N -
        (stabilityError + blockError) ≤ S := by
  linarith [h.stabilitySeam, h.weightedBlockDefect]

/-- Exact finite-error ratio form of the current deduction. -/
theorem WeightedBlockDefectData.ratio
    {S N defect stabilityError blockError : ℝ}
    (h : WeightedBlockDefectData S N defect stabilityError blockError) :
    headline * N - (stabilityError + blockError) / (1 - R / (m : ℝ)) ≤ S := by
  have hden := one_sub_R_div_m_pos
  have hc := h.combined
  rw [headline_eq_normalized]
  rw [show
      ((Hcert - eta * pressureCap * (((m : ℝ) - 1) / (m : ℝ))) /
          (1 - R / (m : ℝ))) * N -
          (stabilityError + blockError) / (1 - R / (m : ℝ)) =
        (((Hcert - eta * pressureCap * (((m : ℝ) - 1) / (m : ℝ))) * N -
          (stabilityError + blockError)) /
          (1 - R / (m : ℝ))) by ring]
  rw [div_le_iff₀ hden]
  linarith

/-- An error bounded by `denominator * eps * N` loses at most `eps` from the
headline coefficient. -/
theorem WeightedBlockDefectData.epsilon_form
    {S N defect stabilityError blockError eps : ℝ}
    (h : WeightedBlockDefectData S N defect stabilityError blockError)
    (herr : stabilityError + blockError ≤
      (1 - R / (m : ℝ)) * eps * N) :
    (headline - eps) * N ≤ S := by
  have hratio := h.ratio
  have hden := one_sub_R_div_m_pos
  have herr' : (stabilityError + blockError) / (1 - R / (m : ℝ)) ≤ eps * N := by
    rw [div_le_iff₀ hden]
    simpa [mul_assoc, mul_comm, mul_left_comm] using herr
  nlinarith

/-- The exact positive error rate still compatible with the rational target. -/
def targetErrorRate : ℝ :=
  (1 - R / (m : ℝ)) * (headline - target)

lemma targetErrorRate_pos : 0 < targetErrorRate := by
  unfold targetErrorRate
  exact mul_pos one_sub_R_div_m_pos (sub_pos.mpr target_lt_headline)

/-- Finite target theorem: this states exactly how small the aggregate error
must be to deduce `673195/10^6` at one height. -/
theorem WeightedBlockDefectData.target_bound
    {S N defect stabilityError blockError : ℝ}
    (h : WeightedBlockDefectData S N defect stabilityError blockError)
    (herr : stabilityError + blockError ≤ targetErrorRate * N) :
    target * N ≤ S := by
  have herr' : stabilityError + blockError ≤
      (1 - R / (m : ℝ)) * (headline - target) * N := by
    simpa [targetErrorRate] using herr
  have hout := h.epsilon_form (eps := headline - target) herr'
  simpa only [sub_sub_cancel] using hout

/-- Abstract asymptotic interface.  `errorsAreSmall` is an epsilon-form
statement that the combined errors are `o(N)`, avoiding any particular height or
counting-function representation on the analytic layer. -/
theorem conditional_capstone
    {X : Type*} {l : Filter X}
    {S N defect stabilityError blockError : X → ℝ}
    (hdata : ∀ᶠ x in l, WeightedBlockDefectData
      (S x) (N x) (defect x) (stabilityError x) (blockError x))
    (errorsAreSmall : ∀ eps > 0, ∀ᶠ x in l,
      stabilityError x + blockError x ≤
        (1 - R / (m : ℝ)) * eps * N x) :
    ∀ eps > 0, ∀ᶠ x in l, (headline - eps) * N x ≤ S x := by
  intro eps heps
  filter_upwards [hdata, errorsAreSmall eps heps] with x hx herr
  exact hx.epsilon_form herr

/-- Specialization of the conditional capstone to the rational coefficient
claimed in the paper. -/
theorem conditional_target
    {X : Type*} {l : Filter X}
    {S N defect stabilityError blockError : X → ℝ}
    (hdata : ∀ᶠ x in l, WeightedBlockDefectData
      (S x) (N x) (defect x) (stabilityError x) (blockError x))
    (errorsAreSmall : ∀ eps > 0, ∀ᶠ x in l,
      stabilityError x + blockError x ≤
        (1 - R / (m : ℝ)) * eps * N x) :
    ∀ᶠ x in l, target * N x ≤ S x := by
  have hmargin : 0 < headline - target := sub_pos.mpr target_lt_headline
  simpa using conditional_capstone hdata errorsAreSmall (headline - target) hmargin

end Zeta23Ext.Current
