import SRWTightness.SourceReferenceIntensity
import SRWTightness.SourceLowerTime
import SRWTightness.EquilibriumEnergyOrder

namespace SRWTightness

noncomputable def sourceEquilibriumTime (b : Site) (m a H : ℝ) : ℝ :=
  equilibriumEnergyTime (translateFinset b (diskFinset (Real.exp 1 * m + H)))
    (translateFinset b (diskFinset a)) (sourceReferenceIntensity m H) (2 / Real.pi)

noncomputable def sourceEquilibriumTimeError : ℝ :=
  diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 1

theorem sourceEquilibriumTimeError_pos : 0 < sourceEquilibriumTimeError := by
  unfold sourceEquilibriumTimeError
  have hB := div_pos diskGreenEnergyConstant_pos (by positivity : 0 < (2 / Real.pi : ℝ))
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  linarith

/-- Actual observation times relative to log(m/a), uniformly on the source killing domain. -/
theorem sourceEquilibriumTime_log_bound (b : Site) (m a H : ℝ)
    (ha : 1 ≤ a) (hma : 2 * a ≤ m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m) :
    |sourceEquilibriumTime b m a H - (Real.log m - Real.log a)| ≤
      sourceEquilibriumTimeError := by
  have hm : 0 < m := by linarith
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hh : |H| ≤ m / 2 := by rw [abs_of_nonneg hH]; linarith
  have hb := capacity_energy_source_bound b m a H ha hma hh
  have hα := sourceReferenceIntensity_bounds m H hm hH hHm
  have hd0 : 0 ≤ sourceReferenceIntensity m H / (2 * (2 / Real.pi)) :=
    div_nonneg hα.1.le (by positivity)
  have hd1 : sourceReferenceIntensity m H / (2 * (2 / Real.pi)) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr (by simpa using hα.2)
  have he : sourceEquilibriumTime b m a H - (Real.log m - Real.log a) =
      (1 / ((2 / Real.pi) * capacity
        (translateFinset b (diskFinset (Real.exp 1 * m + H)))
        (translateFinset b (diskFinset a))) - (Real.log m - Real.log a)) -
          sourceReferenceIntensity m H / (2 * (2 / Real.pi)) := by
    unfold sourceEquilibriumTime equilibriumEnergyTime
    ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hb (by simpa only [abs_of_nonneg hd0] using hd1))

/-- The v_i=d-log(a_i)+O(1) part of (5.9), with the original Green-function d. -/
theorem sourceEquilibriumTime_lowerTime_bound (b : Site) (m a H : ℝ)
    (ha : 1 ≤ a) (hma : 2 * a ≤ m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m) :
    |sourceEquilibriumTime b m a H - (sourceLowerTime m - Real.log a)| ≤
      sourceEquilibriumTimeError + sourceLowerTimeError := by
  have hv := sourceEquilibriumTime_log_bound b m a H ha hma hH hHm
  have hd := sourceLowerTime_log_bound m (by linarith)
  have he : sourceEquilibriumTime b m a H - (sourceLowerTime m - Real.log a) =
      (sourceEquilibriumTime b m a H - (Real.log m - Real.log a)) -
        (sourceLowerTime m - Real.log m) := by ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hv hd)

end SRWTightness
