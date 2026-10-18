import SRWTightness.DiskObservable

open MeasureTheory

namespace SRWTightness

 theorem exitTime_mono_radius {r R : ℝ} (hr : 0 ≤ r) (h : r ≤ R) (ω : Sample) :
    exitTime r ω ≤ exitTime R ω := by
  by_cases ht : exitTime R ω = ⊤
  · rw [ht]
    exact le_top
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [← hk]
    apply (exitTime_le_iff r ω k).mpr
    refine ⟨k, le_rfl, ?_⟩
    have hb := normSq_at_exit_ge R ω k hk.symm
    nlinarith

 theorem ae_diskMax_mono {r R : ℝ} (hr : 0 ≤ r) (h : r ≤ R) :
    ∀ᵐ ω ∂pathLaw, diskMax r ω ≤ diskMax R ω := by
  filter_upwards [exitTime_ne_top_ae hr, exitTime_ne_top_ae (hr.trans h)] with ω hi ho
  have ht := exitTime_mono_radius hr h ω
  rw [← coe_exitSteps r ω hi, ← coe_exitSteps R ω ho] at ht
  exact maxLocalTime_mono ω (WithTop.coe_le_coe.mp ht)

end SRWTightness
