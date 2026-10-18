import SRWTightness.SourceCommonPairDistance
import SRWTightness.SourceCommonPairRadiusLower

namespace SRWTightness

/-- The exact logarithmic ceiling gap gives a tenth-power bound for its exponential. -/
theorem source_common_gap_exp_le (t : ℝ) (ht : 1 ≤ t) :
    Real.exp (-(sourceCommonPairGap t : ℝ)) ≤ 1 / t ^ 10 := by
  have ht0 : 0 < t := by linarith
  have hg := (sourceCommonPairGap_bounds t ht).1
  calc
    _ ≤ Real.exp (-(10 * Real.log t)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / t ^ 10 := by
      rw [Real.exp_neg]
      have he := Real.exp_nat_mul (Real.log t) 10
      norm_num only [Nat.cast_ofNat] at he
      rw [he, Real.exp_log ht0]
      simp only [one_div]

/-- The final coarse level is included: its inner radius is at least the terminal radius over e. -/
theorem source_common_inner_radius_full_range (t : ℝ) (j : ℕ)
    (hj : j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t)) :
    sourceLowerRadius t / Real.exp 1 ≤ sourceCommonPairInnerRadius t j := by
  have h := sourceRecordRadius_ge_terminal (sourceLowerRadius t)
    (sourceLowerRadius_pos t).le (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) j hj
  rw [← sourceRecordRadius_successor] at h
  apply (div_le_iff₀ (Real.exp_pos 1)).mpr
  change sourceLowerRadius t ≤ _
  simpa only [sourceCommonPairInnerRadius, mul_comm] using h

/-- The complete ceiling-gap error, including its linear gap factor, has a decaying majorant. -/
theorem source_common_gap_error_majorant (t : ℝ) (ht : 1 ≤ t) :
    t ^ 2 * (((sourceCommonPairGap t : ℝ) + 1) *
      Real.exp (-(sourceCommonPairGap t : ℝ))) ≤ (10 * Real.log t + 7) / t ^ 8 := by
  have ht0 : 0 < t := by linarith
  have hl := Real.log_nonneg ht
  have hJ := (sourceCommonPairGap_bounds t ht).2
  calc
    _ ≤ t ^ 2 * ((10 * Real.log t + 7) * (1 / t ^ 10)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
      exact mul_le_mul (by linarith) (source_common_gap_exp_le t ht)
        (Real.exp_pos _).le (by positivity)
    _ = (10 * Real.log t + 7) / t ^ 8 := by field_simp <;> ring

end SRWTightness
