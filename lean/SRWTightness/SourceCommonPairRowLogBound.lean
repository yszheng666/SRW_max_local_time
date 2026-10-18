import SRWTightness.SourceCommonPairParameters
import SRWTightness.TranslatedTwoSiteRowLogBound

namespace SRWTightness

/-- The actual common-domain row scale has a uniform logarithmic geometric approximation. -/
theorem source_common_pair_row_log_bound (t : ℝ) (b w : Site) (j : ℕ)
    (hρ : 1 ≤ Real.sqrt (normSq (w - b)))
    (hsep : 4 * Real.sqrt (normSq (w - b)) ≤ sourceCommonPairInnerRadius t j) :
    |sourceCommonPairRowScale t b w j -
      (2 * Real.log (Real.exp 1 * sourceCommonPairInnerRadius t j + 14) -
        Real.log (Real.sqrt (normSq (w - b))))| ≤
      2 * (diskGreenEnergyConstant / (2 / Real.pi) + Real.log 2) + 1 / (2 / Real.pi) := by
  unfold sourceCommonPairRowScale
  rw [sourceCommonPairDomain_eq]
  apply two_site_translated_row_log_bound _ b w hρ
  have hm := sourceCommonPairInnerRadius_pos t j
  nlinarith [Real.exp_one_gt_two]

end SRWTightness
