import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Leading Gaussian tilted mean in any coordinate for the signed pair statistic. -/
theorem pair_tilt_coordinate_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y F G S : Ω → ℝ)
    (hY : MemLp Y 2 μ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (hS : MemLp S 2 μ) :
    covariance Y ((2 : ℝ) • (F + G - S)) μ =
      2 * covariance Y F μ + 2 * covariance Y G μ - 2 * covariance Y S μ := by
  rw [covariance_smul_right, covariance_sub_right hY (hF.add hG) hS,
    covariance_add_right hY hF hG]
  ring

end SRWTightness
