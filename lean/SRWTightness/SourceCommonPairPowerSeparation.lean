import SRWTightness.SourceCommonPairDistance
import SRWTightness.SourceTerminalErrorSmall

namespace SRWTightness

/-- The manuscript logarithmic gap gives the power separation used by terminal mark comparison. -/
theorem source_common_pair_power_separation (t ρ : ℝ) (j : ℕ) (ht : 1 ≤ t)
    (hρ : 0 < ρ)
    (houter : ρ ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (hindex : j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ) :
    2 * ρ ≤ sourceCommonPairInnerRadius t j / t ^ 6 := by
  have ht0 : 0 < t := by linarith
  have hs := (source_common_pair_log_separation t ρ hρ houter j
    (sourceCommonPairGap t) hindex).1
  have hg := (sourceCommonPairGap_bounds t ht).1
  have hl := Real.log_nonneg ht
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog : Real.log (2 * ρ * t ^ 6) ≤ Real.log (sourceCommonPairInnerRadius t j) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hρ.ne', Real.log_pow]
    norm_num
    linarith
  apply (le_div_iff₀ (pow_pos ht0 6)).mpr
  exact (Real.log_le_log_iff (by positivity) (sourceCommonPairInnerRadius_pos t j)).mp hlog

/-- The existing terminal relative-error bound applies at the actual common endpoint radius. -/
theorem source_common_pair_terminal_error_small (W t ρ : ℝ) (j : ℕ)
    (hW : 0 ≤ W) (ht : 2 ≤ t) (hWt : 8 * W ≤ t) (hρ : 1 ≤ ρ)
    (houter : ρ ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (hindex : j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ) :
    W * (2 * ρ + 1) / sourceCommonPairInnerRadius t j *
      Real.log (sourceCommonPairInnerRadius t j / (2 * ρ)) ≤ 1 / 2 := by
  exact source_terminal_error_small W _ (2 * ρ) t hW ht hWt (by linarith)
    (source_common_pair_power_separation t ρ j (by linarith) (by linarith) houter hindex)

end SRWTightness
