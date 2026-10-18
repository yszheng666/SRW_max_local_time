import SRWTightness.BesselExactInverseMoment
import SRWTightness.GaussianHalfIntegralScale

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual inverse radial moment equals a centered Gaussian interval mass divided by x. -/
theorem bessel_inverse_gaussian_interval (T x s : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hs : 0 < s) (hsT : s ≤ T) :
    (∫ ω, (actualBesselThree T x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)) =
      x⁻¹ * (gaussianReal 0 s.toNNReal).real (Set.Icc (-x) x) := by
  rw [bessel_three_exact_inverse_moment T x s hT hx hs hsT,
    gaussian_symmetric_interval s x hs hx.le, gaussian_half_integral_scale s x hs]
  have hS : 0 < Real.sqrt (2 * s) := Real.sqrt_pos.mpr (by positivity)
  rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ 1 / Real.sqrt (2 * s)),
    integral_Ioc_eq_integral_Ioo]
  have hroot : Real.sqrt (2 * Real.pi * s) =
      Real.sqrt Real.pi * Real.sqrt (2 * s) := by
    rw [← Real.sqrt_mul Real.pi_pos.le]
    congr 1
    ring
  rw [hroot]
  field_simp [ne_of_gt hx, ne_of_gt hS, ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]
  <;> ring

end SRWTightness
