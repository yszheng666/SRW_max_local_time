import SRWTightness.ContinuousGridIncrementProbability
import SRWTightness.ScaledGaussianPathLaw

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SRWTightness

/-- The overshoot error in actual Brownian finite-grid reflection tends to zero. -/
theorem scaled_gaussian_grid_increment_decay (T δ : ℝ) (hT : 0 < T) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ gaussianCoefficientLaw.real {ω | ∃ j < 2 ^ n,
      δ < Real.sqrt T * gaussianDyadicPath ω
          (stoppedUniformTimeGrid 0 T (2 ^ n) (j + 1) / T) -
        Real.sqrt T * gaussianDyadicPath ω
          (stoppedUniformTimeGrid 0 T (2 ^ n) j / T)}) atTop (nhds 0) := by
  apply continuous_grid_increment_probability gaussianCoefficientLaw
    (fun t ω ↦ Real.sqrt T * gaussianDyadicPath ω (t / T))
    (fun _ ↦ measurable_const.mul (gaussianDyadicPath_measurable _)) 0 T δ hT.le hδ
  filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
  exact (continuous_const.mul (hω.comp (continuous_id.div_const T))).continuousOn

end SRWTightness
