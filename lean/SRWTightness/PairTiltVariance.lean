import SRWTightness.PairTiltQuadratic
import Mathlib.Probability.Moments.Covariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The signed pair tilt has the manuscript covariance quadratic form. -/
theorem pair_tilt_half_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F G S : Ω → ℝ)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (hS : MemLp S 2 μ)
    (v e : ℝ) (hFS : covariance F S μ = v) (hGS : covariance G S μ = v)
    (hSS : covariance S S μ = v - e) :
    covariance ((2 : ℝ) • (F + G - S)) ((2 : ℝ) • (F + G - S)) μ / 2 =
      2 * covariance F F μ + 2 * covariance G G μ + 4 * covariance F G μ -
        6 * v - 2 * e := by
  rw [covariance_smul_left, covariance_smul_right,
    covariance_sub_sub (hF.add hG) hS (hF.add hG) hS,
    covariance_add_left hF hG (hF.add hG),
    covariance_add_right hF hF hG, covariance_add_right hG hF hG,
    covariance_add_left hF hG hS, covariance_add_right hS hF hG,
    covariance_comm G F, covariance_comm S F, covariance_comm S G,
    hFS, hGS, hSS]
  ring

end SRWTightness
