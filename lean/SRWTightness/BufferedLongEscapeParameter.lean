import SRWTightness.SourceReferenceIntensity

namespace SRWTightness

/-- The reference escape parameter for one short excursion inside a longer buffered annulus. -/
noncomputable def bufferedLongEscapeParameter (ρ H J : ℝ) : ℝ :=
  Real.log ((Real.exp 1 * ρ + H) / (ρ - H)) /
    Real.log ((Real.exp (J + 1) * ρ + H) / (ρ - H))

/-- A positive long-scale gap contains every one-step short-exit overshoot. -/
theorem buffered_long_radius_gap (ρ H J : ℝ) (hρ : 2 ≤ ρ) (hJ : 1 ≤ J) :
    Real.exp 1 * ρ + H + 1 ≤ Real.exp (J + 1) * ρ + H := by
  have he := Real.exp_one_gt_two
  have h2 : 2 * Real.exp 1 ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hE : Real.exp 2 ≤ Real.exp (J + 1) := Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right (h2.trans hE) (show 0 ≤ ρ by linarith)
  nlinarith

/-- The buffered logarithmic parameter is uniformly comparable to the inverse number of scales. -/
theorem buffered_long_escape_parameter_bounds (ρ H J : ℝ) (hρ : 0 < ρ)
    (hH : 0 ≤ H) (hHm : 5 * H ≤ ρ) (hJ : 1 ≤ J) :
    (1 / 2 : ℝ) / (J + 1) ≤ bufferedLongEscapeParameter ρ H J ∧
      bufferedLongEscapeParameter ρ H J ≤ 2 / (J + 1) := by
  have hd : 0 < ρ - H := by linarith
  have he := Real.exp_one_gt_two
  have he0 := Real.exp_pos 1
  have hnumlo : 1 ≤ Real.log ((Real.exp 1 * ρ + H) / (ρ - H)) := by
    have hr : Real.exp 1 ≤ (Real.exp 1 * ρ + H) / (ρ - H) := by
      apply (le_div_iff₀ hd).mpr
      nlinarith [mul_nonneg he0.le hH]
    simpa only [Real.log_exp] using Real.log_le_log he0 hr
  have hnumhi : Real.log ((Real.exp 1 * ρ + H) / (ρ - H)) ≤ 2 := by
    have hg : 0 < (2 / Real.pi : ℝ) := by positivity
    have hh := (sourceReferenceIntensity_bounds ρ H hρ hH hHm).2
    unfold sourceReferenceIntensity at hh
    nlinarith
  have hE : 1 ≤ Real.exp (J + 1) := Real.one_le_exp_iff.mpr (by linarith)
  have hE0 := Real.exp_pos (J + 1)
  have hdenlo : J + 1 ≤ Real.log ((Real.exp (J + 1) * ρ + H) / (ρ - H)) := by
    have hr : Real.exp (J + 1) ≤ (Real.exp (J + 1) * ρ + H) / (ρ - H) := by
      apply (le_div_iff₀ hd).mpr
      nlinarith [mul_nonneg hE0.le hH]
    simpa only [Real.log_exp] using Real.log_le_log hE0 hr
  have hdenhi : Real.log ((Real.exp (J + 1) * ρ + H) / (ρ - H)) ≤ J + 2 := by
    have hr : (Real.exp (J + 1) * ρ + H) / (ρ - H) ≤ 2 * Real.exp (J + 1) := by
      apply (div_le_iff₀ hd).mpr
      have hm := mul_le_mul_of_nonneg_left hHm hE0.le
      have hEH := mul_le_mul_of_nonneg_right hE hH
      nlinarith
    have he' : 2 * Real.exp (J + 1) ≤ Real.exp (J + 2) := by
      rw [show J + 2 = 1 + (J + 1) by ring, Real.exp_add 1 (J + 1)]
      exact mul_le_mul_of_nonneg_right he.le hE0.le
    have hpositive : 0 < (Real.exp (J + 1) * ρ + H) / (ρ - H) := by positivity
    simpa only [Real.log_exp] using Real.log_le_log hpositive (hr.trans he')
  have hden0 : 0 < Real.log ((Real.exp (J + 1) * ρ + H) / (ρ - H)) := by linarith
  have hJ1 : 0 < J + 1 := by linarith
  have hJ2 : 0 < J + 2 := by linarith
  unfold bufferedLongEscapeParameter
  constructor
  · calc
      (1 / 2 : ℝ) / (J + 1) ≤ 1 / (J + 2) := by
        apply (div_le_div_iff₀ hJ1 hJ2).mpr
        linarith
      _ ≤ 1 / Real.log ((Real.exp (J + 1) * ρ + H) / (ρ - H)) :=
        div_le_div_of_nonneg_left (by norm_num) hden0 hdenhi
      _ ≤ _ := div_le_div_of_nonneg_right hnumlo hden0.le
  · calc
      _ ≤ 2 / Real.log ((Real.exp (J + 1) * ρ + H) / (ρ - H)) :=
        div_le_div_of_nonneg_right hnumhi hden0.le
      _ ≤ 2 / (J + 1) := div_le_div_of_nonneg_left (by norm_num) hJ1 hdenlo

end SRWTightness
