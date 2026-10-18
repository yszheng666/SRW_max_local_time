import SRWTightness.BesselInverseGaussianInterval
import SRWTightness.BesselInverseMomentInternal

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SRWTightness

/-- The fixed Gaussian survival interval has an explicit uniform inverse-square-root bound. -/
theorem gaussian_survival_mass_bound (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    (gaussianReal 0 T.toNNReal).real (Set.Icc (-x) x) ≤
      (x * besselInverseMomentConstant) / Real.sqrt T := by
  have hi := (bessel_three_inverse_moment_input_internal.2 T x T hT hx hT le_rfl).2
  rw [bessel_inverse_gaussian_interval T x T hT hx hT le_rfl] at hi
  have hh := mul_le_mul_of_nonneg_left hi hx.le
  calc
    _ = x * (x⁻¹ * (gaussianReal 0 T.toNNReal).real (Set.Icc (-x) x)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]
    _ ≤ x * (besselInverseMomentConstant / Real.sqrt T) := hh
    _ = _ := by ring

/-- Survival above zero tends to zero over arbitrarily large Brownian horizons. -/
theorem gaussian_survival_mass_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (fun T : ℝ ↦ (gaussianReal 0 T.toNNReal).real (Set.Icc (-x) x))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun T ↦ measureReal_nonneg))
    (g := fun T : ℝ ↦ (x * besselInverseMomentConstant) / Real.sqrt T)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact gaussian_survival_mass_bound T x hT hx
  · exact Real.tendsto_sqrt_atTop.const_div_atTop (x * besselInverseMomentConstant)

end SRWTightness
