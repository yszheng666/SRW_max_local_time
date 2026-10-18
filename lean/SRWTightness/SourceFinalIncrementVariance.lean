import SRWTightness.SourcePointEnergyTime
import SRWTightness.SourceEquilibriumTime

namespace SRWTightness

/-- The final site increment variance stays within a fixed additive error of log(a). -/
theorem source_final_increment_variance_log_bound (b : Site) (m a H : ℝ)
    (ha : 1 ≤ a) (hma : 2 * a ≤ m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m) :
    |(sourcePointEnergyTime b m H - sourceEquilibriumTime b m a H) - Real.log a| ≤
      sourcePointEnergyTimeError + sourceEquilibriumTimeError := by
  have hV := sourcePointEnergyTime_log_bound b m H (by linarith) hH hHm
  have hv := sourceEquilibriumTime_log_bound b m a H ha hma hH hHm
  have he : (sourcePointEnergyTime b m H - sourceEquilibriumTime b m a H) - Real.log a =
      (sourcePointEnergyTime b m H - Real.log m) -
        (sourceEquilibriumTime b m a H - (Real.log m - Real.log a)) := by ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hV hv)

end SRWTightness
