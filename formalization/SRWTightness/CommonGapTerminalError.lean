import SRWTightness.SourceCommonPairDistance

namespace SRWTightness

/-- The actual floor bracket bounds the terminal observation error for any admissible gap.
This uses the gap itself and does not replace it by a time-dependent lower bound. -/
theorem source_common_gap_terminal_error (W t ρ : ℝ) (j J : ℕ)
    (hW : 0 ≤ W) (hρ : 1 ≤ ρ)
    (houter : ρ ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (hindex : j + J = sourceCommonPairDistanceIndex t ρ)
    (hsep : 2 * ρ ≤ sourceCommonPairInnerRadius t j) :
    W * (2 * ρ + 1) / sourceCommonPairInnerRadius t j *
      Real.log (sourceCommonPairInnerRadius t j / (2 * ρ)) ≤
        3 * Real.exp 1 * W * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) := by
  let r := sourceCommonPairInnerRadius t j
  have hr : 0 < r := sourceCommonPairInnerRadius_pos t j
  have hρ0 : 0 < ρ := by linarith
  have hb := source_common_pair_log_separation t ρ hρ0 houter j J hindex
  have he := Real.exp_le_exp.mpr
    (show Real.log ρ - Real.log r ≤ 1 - (J : ℝ) by dsimp [r]; linarith [hb.1])
  rw [Real.exp_sub, Real.exp_log hρ0, Real.exp_log hr] at he
  have hratio : (2 * ρ + 1) / r ≤ 3 * Real.exp (1 - (J : ℝ)) := by
    calc
      _ ≤ (3 * ρ) / r := div_le_div_of_nonneg_right (by linarith) hr.le
      _ = 3 * (ρ / r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by norm_num)
  have hlog0 : 0 ≤ Real.log (r / (2 * ρ)) :=
    Real.log_nonneg ((one_le_div (by positivity)).mpr hsep)
  have hlog : Real.log (r / (2 * ρ)) ≤ (J : ℝ) + 1 := by
    rw [Real.log_div hr.ne' (by positivity), Real.log_mul (by norm_num) hρ0.ne']
    have htwo := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    dsimp [r]
    linarith [hb.2]
  calc
    _ = W * ((2 * ρ + 1) / r) * Real.log (r / (2 * ρ)) := by dsimp [r]; ring
    _ ≤ W * (3 * Real.exp (1 - (J : ℝ))) * Real.log (r / (2 * ρ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hW) hlog0
    _ ≤ W * (3 * Real.exp (1 - (J : ℝ))) * ((J : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

end SRWTightness
