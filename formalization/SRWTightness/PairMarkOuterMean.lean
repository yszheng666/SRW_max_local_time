import SRWTightness.PairTiltMeanCoordinates
import SRWTightness.PairEquilibriumCovariance
import SRWTightness.EquilibriumEnergyOrder
import SRWTightness.DiskCapacityLogBound

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A separated outer equilibrium average has exactly twice its energy time as leading tilted mean. -/
theorem pair_mark_tilt_outer_average_mean (D M : Finset Site) (b : Site) (a r : ℝ)
    (ha : 0 < a) (hr : 2 ≤ r) (har : a ≤ r - 1)
    (hRM : translateFinset b (diskFinset r) ⊆ M) (hMD : M ⊆ D)
    (z y : M) (hz : Real.sqrt (normSq ((z : Site) - b)) < r - 1)
    (hy : Real.sqrt (normSq ((y : Site) - b)) < r - 1)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D M ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let μ := markProductLaw D M α k
    let F := normalizedMarkSum M k α g u z
    let G := normalizedMarkSum M k α g u y
    let S := normalizedEquilibriumAverage D M (translateFinset b (diskFinset a)) k α g u
    let Y := normalizedEquilibriumAverage D M (translateFinset b (diskFinset r)) k α g u
    covariance Y ((2 : ℝ) • (F + G - S)) μ =
      2 * equilibriumEnergyTime D (translateFinset b (diskFinset r)) α g := by
  letI := markProductLaw_isProbabilityMeasure D M α hα.le hcap k
  have hKR : translateFinset b (diskFinset a) ⊆ translateFinset b (diskFinset r) := by
    apply Finset.image_subset_image
    exact diskFinset_mono a r ha.le (by linarith)
  have hne : (translateFinset b (diskFinset a)).Nonempty := by
    refine ⟨b, ?_⟩
    rw [mem_translateFinset_iff, sub_self]
    exact zero_mem_diskFinset a ha
  apply pair_tilt_outer_average_mean
    (markProductLaw D M α k) _ _ _ _
    (normalizedEquilibriumAverage_memLp_two D M _ α g u hα.le hcap k)
    (normalizedMarkSum_memLp_two D M α g u hα.le hcap k z)
    (normalizedMarkSum_memLp_two D M α g u hα.le hcap k y)
    (normalizedEquilibriumAverage_memLp_two D M _ α g u hα.le hcap k)
  · rw [covariance_comm]
    exact normalizedEquilibriumAverage_interior_covariance D M b r hr hRM hMD z hz
      α g u hα hg hu hcap k hk
  · rw [covariance_comm]
    exact normalizedEquilibriumAverage_interior_covariance D M b r hr hRM hMD y hy
      α g u hα hg hu hcap k hk
  · rw [covariance_comm]
    exact normalizedEquilibriumAverage_covariance_nested D M _ _ hKR hRM hMD hne
      (translated_disk_equilibriumWeight_disjoint D b a r ha.le hr har (hRM.trans hMD))
      α g u hα hg hu hcap k hk

end SRWTightness
