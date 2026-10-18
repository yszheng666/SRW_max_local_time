import SRWTightness.SourceOriginGreenBound
import SRWTightness.EquilibriumEnergyOrder

namespace SRWTightness

theorem pointEnergyTime_translate (b : Site) (D : Finset Site) (z : Site) (α g : ℝ) :
    pointEnergyTime (translateFinset b D) (b + z) α g = pointEnergyTime D z α g := by
  simp only [pointEnergyTime, killedGreen_translate]

noncomputable def sourcePointEnergyTime (b : Site) (m H : ℝ) : ℝ :=
  pointEnergyTime (translateFinset b (diskFinset (Real.exp 1 * m + H))) b
    (sourceReferenceIntensity m H) (2 / Real.pi)

noncomputable def sourcePointEnergyTimeError : ℝ :=
  diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 +
    (1 + 2 * (2 / Real.pi)) / (2 * (2 / Real.pi))

/-- The exact source center-point variance time V is log(m)+O(1), uniformly in its center. -/
theorem sourcePointEnergyTime_log_bound (b : Site) (m H : ℝ)
    (hm : 2 ≤ m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m) :
    |sourcePointEnergyTime b m H - Real.log m| ≤ sourcePointEnergyTimeError := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hα := sourceReferenceIntensity_bounds m H (by linarith) hH hHm
  have hG := sourceOriginGreen_log_bound m H hm hH hHm
  have he : sourcePointEnergyTime b m H - Real.log m =
      (diskGreen (Real.exp 1 * m + H) 0 0 / (2 / Real.pi) - Real.log m) -
        (1 + sourceReferenceIntensity m H) / (2 * (2 / Real.pi)) := by
    unfold sourcePointEnergyTime
    have hh := pointEnergyTime_translate b (diskFinset (Real.exp 1 * m + H)) 0
      (sourceReferenceIntensity m H) (2 / Real.pi)
    simp only [add_zero] at hh
    rw [hh]
    unfold pointEnergyTime diskGreen
    ring
  have hnon : 0 ≤ (1 + sourceReferenceIntensity m H) / (2 * (2 / Real.pi)) := by
    apply div_nonneg _ (by positivity)
    linarith [hα.1]
  have hu : (1 + sourceReferenceIntensity m H) / (2 * (2 / Real.pi)) ≤
      (1 + 2 * (2 / Real.pi)) / (2 * (2 / Real.pi)) :=
    div_le_div_of_nonneg_right (by linarith [hα.2]) (by positivity)
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hG (by simpa only [abs_of_nonneg hnon] using hu))

/-- The V=d+O(1) assertion in the source single-observation covariance formula. -/
theorem sourcePointEnergyTime_lowerTime_bound (b : Site) (m H : ℝ)
    (hm : 2 ≤ m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m) :
    |sourcePointEnergyTime b m H - sourceLowerTime m| ≤
      sourcePointEnergyTimeError + sourceLowerTimeError := by
  have hV := sourcePointEnergyTime_log_bound b m H hm hH hHm
  have hd := sourceLowerTime_log_bound m hm
  have he : sourcePointEnergyTime b m H - sourceLowerTime m =
      (sourcePointEnergyTime b m H - Real.log m) - (sourceLowerTime m - Real.log m) := by ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hV hd)

end SRWTightness
