import SRWTightness.SourceCommonPairEndpoint
import SRWTightness.SourceReferenceIntensityError

namespace SRWTightness

/-- The actual common intensity gives a uniform relative square-root normalization error. -/
theorem source_common_pair_sqrt_intensity_error (t : ℝ) (j : ℕ)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j) :
    |Real.sqrt (sourceCommonPairIntensity t j / (2 / Real.pi)) - 1| ≤
      56 / sourceCommonPairInnerRadius t j := by
  let g : ℝ := 2 / Real.pi
  let m := sourceCommonPairInnerRadius t j
  let α := sourceCommonPairIntensity t j
  have hg : 0 < g := by dsimp [g]; positivity
  have hm0 : 0 < m := sourceCommonPairInnerRadius_pos t j
  have hlo := (sourceReferenceIntensity_error m 14 hm0 (by norm_num) (by dsimp [m]; linarith)).1
  have hhi := (abs_le.mp (sourceReferenceIntensity_fourteen_error m hm)).2
  change 0 ≤ α - g at hlo
  change α - g ≤ 56 * g / m at hhi
  have hr : 1 ≤ α / g := (one_le_div hg).mpr (by linarith)
  have hs : 1 ≤ Real.sqrt (α / g) := by simpa using Real.sqrt_le_sqrt hr
  have hsq := Real.sq_sqrt (show 0 ≤ α / g by linarith)
  have hdiff : α / g - 1 = (α - g) / g := by field_simp
  have hb : α / g - 1 ≤ 56 / m := by
    rw [hdiff]
    calc
      (α - g) / g ≤ (56 * g / m) / g := div_le_div_of_nonneg_right hhi hg.le
      _ = 56 / m := by field_simp
  change |Real.sqrt (α / g) - 1| ≤ 56 / m
  rw [abs_of_nonneg (by linarith)]
  nlinarith

/-- The endpoint perturbation has an explicit inverse-inner-radius bound. -/
theorem source_common_pair_endpoint_error (t : ℝ) (j : ℕ)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j) :
    |sourceCommonPairScaledEndpoint t j - sourceCommonPairEndpoint t j| ≤
      56 * |sourceCommonPairEndpoint t j| / sourceCommonPairInnerRadius t j := by
  have hs := source_common_pair_sqrt_intensity_error t j hm
  unfold sourceCommonPairScaledEndpoint
  rw [show Real.sqrt (sourceCommonPairIntensity t j / (2 / Real.pi)) *
      sourceCommonPairEndpoint t j - sourceCommonPairEndpoint t j =
      (Real.sqrt (sourceCommonPairIntensity t j / (2 / Real.pi)) - 1) *
        sourceCommonPairEndpoint t j by ring, abs_mul]
  calc
    _ ≤ (56 / sourceCommonPairInnerRadius t j) * |sourceCommonPairEndpoint t j| :=
      mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    _ = _ := by ring

end SRWTightness
