import SRWTightness.PairTiltMeanCoordinates
import SRWTightness.PairEquilibriumCovariance
import SRWTightness.EquilibriumEnergyOrder
import SRWTightness.DiskCapacityLogBound

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The last actual equilibrium average has the positive discrete correction in its leading tilted mean. -/
theorem pair_mark_tilt_last_average_mean (D M : Finset Site) (b : Site) (a : ℝ)
    (ha : 2 ≤ a) (hKM : translateFinset b (diskFinset a) ⊆ M) (hMD : M ⊆ D)
    (z y : M) (hz : Real.sqrt (normSq ((z : Site) - b)) < a - 1)
    (hy : Real.sqrt (normSq ((y : Site) - b)) < a - 1)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D M ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let μ := markProductLaw D M α k
    let F := normalizedMarkSum M k α g u z
    let G := normalizedMarkSum M k α g u y
    let S := normalizedEquilibriumAverage D M (translateFinset b (diskFinset a)) k α g u
    let v := equilibriumEnergyTime D (translateFinset b (diskFinset a)) α g
    let e := (∑ x ∈ translateFinset b (diskFinset a),
      equilibriumWeight D (translateFinset b (diskFinset a)) x ^ 2) / (2 * g)
    covariance S ((2 : ℝ) • (F + G - S)) μ = 2 * v + 2 * e := by
  letI := markProductLaw_isProbabilityMeasure D M α hα.le hcap k
  have hne : (translateFinset b (diskFinset a)).Nonempty := by
    refine ⟨b, ?_⟩
    rw [mem_translateFinset_iff, sub_self]
    exact zero_mem_diskFinset a (by linarith)
  apply pair_tilt_last_average_mean
    (markProductLaw D M α k) _ _ _
    (normalizedMarkSum_memLp_two D M α g u hα.le hcap k z)
    (normalizedMarkSum_memLp_two D M α g u hα.le hcap k y)
    (normalizedEquilibriumAverage_memLp_two D M _ α g u hα.le hcap k)
  · exact normalizedEquilibriumAverage_interior_covariance D M b a ha hKM hMD z hz
      α g u hα hg hu hcap k hk
  · exact normalizedEquilibriumAverage_interior_covariance D M b a ha hKM hMD y hy
      α g u hα hg hu hcap k hk
  · exact normalizedEquilibriumAverage_covariance_self D M _ hKM hMD hne
      α g u hα hg hu hcap k hk

end SRWTightness
