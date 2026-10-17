import SRWTightness.PotentialKernelRadialBounds
import SRWTightness.PotentialKernelGreen
import SRWTightness.ExitMoment
import SRWTightness.GeometryTriangle

open MeasureTheory Filter

namespace SRWTightness

theorem normSq_disk_exit_sub_le (R : ℝ) (hR : 1 ≤ R) (y : Site) (hy : y ∈ disk R) :
    ∀ᵐ ω ∂pathLaw, normSq (domainExitLocation (diskFinset R) 0 ω - y) ≤ (3 * R) ^ 2 := by
  filter_upwards [normSq_exitSteps_bounds (by linarith : 0 ≤ R)] with ω hω
  have hy' : normSq (-y) ≤ R ^ 2 := by rw [normSq_neg]; exact (show normSq y < R ^ 2 from hy).le
  have hh := normSq_add_bound (position ω (exitSteps R ω)) (-y)
    (by linarith : 0 ≤ R + 1) (by linarith : 0 ≤ R) hω.2 hy'
  simp only [domainExitLocation, domainSteps_disk, zero_add, sub_eq_add_neg]
  exact hh.trans (by nlinarith)

theorem exitPayoff_potential_disk_upper (R : ℝ) (hR : 1 ≤ R) (y : Site) (hy : y ∈ disk R) :
    exitPayoff (diskFinset R) (fun w ↦ potentialKernel (w - y)) 0 ≤
      Real.log ((3 * R) ^ 2) / Real.pi + potentialUpperConstant := by
  unfold exitPayoff
  calc
    _ ≤ ∫ _ω : Sample, Real.log ((3 * R) ^ 2) / Real.pi + potentialUpperConstant ∂pathLaw := by
      apply integral_mono_ae (integrable_domainExit_payoff (diskFinset R) 0 (fun w ↦ potentialKernel (w - y))) (integrable_const _)
      filter_upwards [normSq_disk_exit_sub_le R hR y hy] with ω hω
      exact potentialKernel_le_log_normBound _ _ (by nlinarith) hω
    _ = _ := by simp

end SRWTightness
