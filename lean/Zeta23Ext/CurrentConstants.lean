/-
Exact constants for the 0.673195 current-result deduction.

This module is deliberately independent of the older Montgomery--Taylor,
uniform-weight capstone in `Zeta23Ext.Final`.  In particular, nothing here
asserts that its `m = 267` certificate proves the present `m = 250` result.
-/
import Mathlib

noncomputable section

namespace Zeta23Ext.Current

/-- Certified lower bound for the weighted seven-point functional. -/
def beta : ℝ := 509 / 100000

/-- Number of gaps in one seven-point window. -/
def q : ℕ := 6

/-- Block size used by the current optimization. -/
def m : ℕ := 250

/-- Linear pressure coefficient in the local functional. -/
def pressure : ℝ := 1 / 2300

/-- Maximum accumulated pressure of a single block gap. -/
def pressureCap : ℝ := 3 / 1150

/-- Certified analytic stability constant for the current window. -/
def Hcert : ℝ := 672457 / 1000000

/-- Rational headline claimed by the paper. -/
def target : ℝ := 673195 / 1000000

/-- Accumulated local energy before application of the sharp defect profile. -/
def A : ℝ := 31049 / 25000

/-- Sharp block reward `h(A)`, where `A > 1`. -/
def R : ℝ := 2 * Real.sqrt A - 1

/-- Chord slope of the sharp profile on `[0,A]`. -/
def eta : ℝ := R / A

/-- Exact coefficient produced by the finite/asymptotic deduction. -/
def headline : ℝ :=
  ((m : ℝ) * Hcert - eta * pressureCap * ((m : ℝ) - 1)) /
    ((m : ℝ) - R)

lemma beta_pos : 0 < beta := by unfold beta; norm_num
lemma pressure_pos : 0 < pressure := by unfold pressure; norm_num
lemma pressureCap_pos : 0 < pressureCap := by unfold pressureCap; norm_num
lemma Hcert_pos : 0 < Hcert := by unfold Hcert; norm_num
lemma target_pos : 0 < target := by unfold target; norm_num
lemma A_pos : 0 < A := by unfold A; norm_num

lemma m_eq : m = 250 := rfl
lemma q_eq : q = 6 := rfl
lemma pressureCap_eq_six_mul : pressureCap = 6 * pressure := by
  unfold pressureCap pressure
  norm_num

/-- `A = beta * (m - q)` with all casts made explicit. -/
lemma A_eq_beta_mul : A = beta * ((m : ℝ) - (q : ℝ)) := by
  unfold A beta m q
  norm_num

lemma one_lt_A : 1 < A := by unfold A; norm_num

lemma sqrtA_sq : Real.sqrt A ^ 2 = A := Real.sq_sqrt A_pos.le

/-- A coarse rational lower enclosure, already strong enough for the final comparison. -/
lemma sqrtA_lower : (278567 : ℝ) / 250000 < Real.sqrt A := by
  have hs := sqrtA_sq
  have hs0 := Real.sqrt_nonneg A
  unfold A at hs hs0 ⊢
  nlinarith

lemma sqrtA_lt_two : Real.sqrt A < 2 := by
  have hs := sqrtA_sq
  have hs0 := Real.sqrt_nonneg A
  unfold A at hs hs0 ⊢
  nlinarith

lemma R_lower : (153567 : ℝ) / 125000 < R := by
  unfold R
  linarith [sqrtA_lower]

lemma R_pos : 0 < R := lt_trans (by norm_num) R_lower

lemma R_lt_three : R < 3 := by
  unfold R
  linarith [sqrtA_lt_two]

lemma eta_pos : 0 < eta := div_pos R_pos A_pos

lemma block_denominator_pos : 0 < (m : ℝ) - R := by
  rw [m_eq]
  norm_num at *
  linarith [R_lt_three]

lemma one_sub_R_div_m_pos : 0 < 1 - R / (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by rw [m_eq]; norm_num
  rw [sub_pos, div_lt_one hm0]
  linarith [block_denominator_pos]

/-- Exact identity between the two convenient presentations of the coefficient. -/
lemma headline_eq_normalized :
    headline =
      (Hcert - eta * pressureCap * (((m : ℝ) - 1) / (m : ℝ))) /
        (1 - R / (m : ℝ)) := by
  unfold headline
  have hm0 : ((m : ℝ) : ℝ) ≠ 0 := by rw [m_eq]; norm_num
  field_simp

/-- Kernel-checked comparison behind the printed decimal headline. -/
theorem target_lt_headline : target < headline := by
  rw [headline_eq_normalized, lt_div_iff₀ one_sub_R_div_m_pos]
  have hR := R_lower
  have hc : target - pressureCap * (((m : ℝ) - 1) / A) =
      (21449345153 : ℝ) / 142825400000 := by
    unfold target pressureCap m A
    norm_num
  have hcpos : 0 < target - pressureCap * (((m : ℝ) - 1) / A) := by
    rw [hc]
    norm_num
  have hkey : 0 < (m : ℝ) * (Hcert - target) +
      R * (target - pressureCap * (((m : ℝ) - 1) / A)) := by
    have hmterm : (m : ℝ) * (Hcert - target) = -(369 : ℝ) / 2000 := by
      unfold m Hcert target
      norm_num
    rw [hmterm, hc]
    nlinarith
  have hid : (m : ℝ) *
        ((Hcert - eta * pressureCap * (((m : ℝ) - 1) / (m : ℝ))) -
          target * (1 - R / (m : ℝ))) =
      (m : ℝ) * (Hcert - target) +
        R * (target - pressureCap * (((m : ℝ) - 1) / A)) := by
    unfold eta m
    field_simp [A_pos.ne']
    ring
  have hm0 : (0 : ℝ) < (m : ℝ) := by rw [m_eq]; norm_num
  nlinarith [hkey, hid]

lemma headline_pos : 0 < headline := lt_trans target_pos target_lt_headline

end Zeta23Ext.Current
