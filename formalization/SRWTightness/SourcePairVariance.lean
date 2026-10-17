import SRWTightness.PairMarkVariance
import SRWTightness.SourceReferenceIntensity
import SRWTightness.SourceLowerTime

open MeasureTheory ProbabilityTheory

namespace SRWTightness

noncomputable def sourcePairVarianceError : ℝ :=
  diskGreenEnergyConstant / (2 / Real.pi) + Real.log 2 + Real.log 4 +
    1 + 1 / (2 * (2 / Real.pi)) + sourceLowerTimeError

/-- Each interior site's actual mark variance equals the manuscript time d up to a fixed error. -/
theorem source_pair_variance (b : Site) (m H : ℝ) (hm : 2 ≤ m) (hH : 0 ≤ H)
    (hHm : 5 * H ≤ m) (M : Finset Site)
    (hMD : M ⊆ translateFinset b (diskFinset (Real.exp 1 * m + H))) (y : M)
    (hy : normSq ((y : Site) - b) ≤ ((Real.exp 1 * m + H) / 2) ^ 2)
    (u : ℝ) (hu : 0 < u)
    (hcap : sourceReferenceIntensity m H *
      capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) M ≤ 1)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    |covariance (normalizedMarkSum M k (sourceReferenceIntensity m H) (2 / Real.pi) u y)
      (normalizedMarkSum M k (sourceReferenceIntensity m H) (2 / Real.pi) u y)
      (markProductLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) M
        (sourceReferenceIntensity m H) k) - sourceLowerTime m| ≤ sourcePairVarianceError := by
  have hm0 : 0 < m := by linarith
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hR : 4 ≤ Real.exp 1 * m + H := by nlinarith [Real.exp_one_gt_two]
  have hRm : m ≤ Real.exp 1 * m + H := by nlinarith [Real.exp_one_gt_two]
  have hR4 : Real.exp 1 * m + H ≤ 4 * m := by nlinarith [Real.exp_one_lt_three]
  have hα := sourceReferenceIntensity_bounds m H hm0 hH hHm
  have hb := pair_mark_variance_log_radius b _ hR M hMD y hy
    (sourceReferenceIntensity m H) u hα.1 hu hcap k hk
  have hd := sourceLowerTime_log_bound m hm
  have hl := Real.log_le_log hm0 hRm
  have hh := Real.log_le_log (by linarith : 0 < Real.exp 1 * m + H) hR4
  rw [Real.log_mul (by norm_num) hm0.ne'] at hh
  have hαpos : 0 < sourceReferenceIntensity m H := hα.1
  have ha0 : 0 ≤ (1 + sourceReferenceIntensity m H) / (2 * (2 / Real.pi)) := by positivity
  have ha1 : (1 + sourceReferenceIntensity m H) / (2 * (2 / Real.pi)) ≤
      1 + 1 / (2 * (2 / Real.pi)) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have he : 1 / (2 * (2 / Real.pi)) * (2 * (2 / Real.pi)) = 1 :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [hα.2]
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  unfold sourcePairVarianceError
  apply abs_le.mpr
  constructor <;> linarith

end SRWTightness
