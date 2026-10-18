import SRWTightness.SourcePairCovarianceBounds
import SRWTightness.PairTiltMeanCoordinates
import SRWTightness.PairEquilibriumCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Both actual site coordinates have leading tilted mean 2d with a uniform error. -/
theorem source_pair_site_mean_bound (b : Site) (m H a L : ℝ)
    (hm : 2 ≤ m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m) (hma : 2 * a ≤ m)
    (M : Finset Site) (hMD : M ⊆ translateFinset b (diskFinset (Real.exp 1 * m + H)))
    (z y : M) (hz : (z : Site) = b)
    (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ a)
    (hhi : a ≤ L * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : 0 < u)
    (hcap : sourceReferenceIntensity m H *
      capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) M ≤ 1)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ))
    (hKM : translateFinset b (diskFinset a) ⊆ M)
 :
    let α := sourceReferenceIntensity m H
    let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
    let μ := markProductLaw D M α k
    let F := normalizedMarkSum M k α (2 / Real.pi) u
    let S := normalizedEquilibriumAverage D M (translateFinset b (diskFinset a)) k α (2 / Real.pi) u
    let X := (2 : ℝ) • (F z + F y - S)
    let E := 2 * sourcePairVarianceError +
      2 * (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 + Real.log L)
    |covariance (F z) X μ - 2 * sourceLowerTime m| ≤ E ∧
    |covariance (F y) X μ - 2 * sourceLowerTime m| ≤ E := by
  let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
  let α := sourceReferenceIntensity m H
  let μ := markProductLaw D M α k
  let F := normalizedMarkSum M k α (2 / Real.pi) u
  let S := normalizedEquilibriumAverage D M (translateFinset b (diskFinset a)) k α (2 / Real.pi) u
  have hα := (sourceReferenceIntensity_bounds m H (by linarith) hH hHm).1
  letI := markProductLaw_isProbabilityMeasure D M α hα.le hcap k
  have ha : 2 ≤ a := by linarith
  have hzi : Real.sqrt (normSq ((z : Site) - b)) < a - 1 := by
    rw [hz, sub_self]
    norm_num [normSq]
    linarith
  have hyi : Real.sqrt (normSq ((y : Site) - b)) < a - 1 := by linarith
  have hFS := normalizedEquilibriumAverage_interior_covariance D M b a ha hKM hMD z hzi
    α (2 / Real.pi) u hα (by positivity) hu hcap k hk
  have hGS := normalizedEquilibriumAverage_interior_covariance D M b a ha hKM hMD y hyi
    α (2 / Real.pi) u hα (by positivity) hu hcap k hk
  have hF := normalizedMarkSum_memLp_two D M α (2 / Real.pi) u hα.le hcap k z
  have hG := normalizedMarkSum_memLp_two D M α (2 / Real.pi) u hα.le hcap k y
  have hS := normalizedEquilibriumAverage_memLp_two D M (translateFinset b (diskFinset a)) α (2 / Real.pi) u hα.le hcap k
  obtain ⟨hzv, hyv, hcross⟩ := source_pair_covariance_bounds b m H a L hm hH hHm hma
    M hMD z y hz hρ hlo hhi u hu hcap k hk
  dsimp only
  constructor
  · exact pair_tilt_site_mean_error μ (F z) (F y) S hF hG hS
      (sourceLowerTime m) (sourceEquilibriumTime b m a H) _ _ hFS hzv hcross
  · have hrev : |covariance (F y) (F z) μ - sourceEquilibriumTime b m a H| ≤
        2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 + Real.log L := by
      rw [covariance_comm]
      exact hcross
    have hh := pair_tilt_site_mean_error μ (F y) (F z) S hG hF hS
      (sourceLowerTime m) (sourceEquilibriumTime b m a H) _ _ hGS hyv hrev
    rw [add_comm (F y) (F z)] at hh
    exact hh

end SRWTightness
