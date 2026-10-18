import SRWTightness.SourcePairVariance
import SRWTightness.PairResidualCrossBound
import SRWTightness.SourceEquilibriumTime

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- All three residual entries for the same actual reference-mark law. -/
theorem source_pair_covariance_bounds (b : Site) (m H a L : ℝ)
    (hm : 2 ≤ m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m) (hma : 2 * a ≤ m)
    (M : Finset Site) (hMD : M ⊆ translateFinset b (diskFinset (Real.exp 1 * m + H)))
    (z y : M) (hz : (z : Site) = b)
    (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ a)
    (hhi : a ≤ L * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : 0 < u)
    (hcap : sourceReferenceIntensity m H *
      capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) M ≤ 1)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let α := sourceReferenceIntensity m H
    let μ := markProductLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) M α k
    let F := normalizedMarkSum M k α (2 / Real.pi) u
    |covariance (F z) (F z) μ - sourceLowerTime m| ≤ sourcePairVarianceError ∧
    |covariance (F y) (F y) μ - sourceLowerTime m| ≤ sourcePairVarianceError ∧
    |covariance (F z) (F y) μ - sourceEquilibriumTime b m a H| ≤
      2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 + Real.log L := by
  have hm0 : 0 < m := by linarith
  have hRm : m ≤ Real.exp 1 * m + H := by nlinarith [Real.exp_one_gt_two]
  have hy : normSq ((y : Site) - b) ≤ ((Real.exp 1 * m + H) / 2) ^ 2 := by
    have hs := Real.sq_sqrt (normSq_nonneg ((y : Site) - b))
    have hn := Real.sqrt_nonneg (normSq ((y : Site) - b))
    nlinarith
  have hzinner : normSq ((z : Site) - b) ≤ ((Real.exp 1 * m + H) / 2) ^ 2 := by
    rw [hz, sub_self]
    norm_num [normSq]
    positivity
  have hα := (sourceReferenceIntensity_bounds m H hm0 hH hHm).1
  refine ⟨source_pair_variance b m H hm hH hHm M hMD z hzinner u hu hcap k hk,
    source_pair_variance b m H hm hH hHm M hMD y hy u hu hcap k hk, ?_⟩
  exact pair_residual_cross_bound b (Real.exp 1 * m + H) a L M hMD z y hz hρ hlo hhi
    (by linarith) (sourceReferenceIntensity m H) u hα hu hcap k hk

end SRWTightness
