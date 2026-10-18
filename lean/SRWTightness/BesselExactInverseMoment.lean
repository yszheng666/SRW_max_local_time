import SRWTightness.RadialLaplaceExactIntegral
import SRWTightness.BesselSharpInverseMoment

open MeasureTheory
namespace SRWTightness

/-- The actual inverse radial moment has an exact finite Gaussian integral formula. -/
theorem bessel_three_exact_inverse_moment (T x s : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hs : 0 < s) (hsT : s ≤ T) :
    (∫ ω, (actualBesselThree T x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)) =
      (2 / Real.sqrt Real.pi) *
        ∫ u in Set.Ioo 0 (1 / Real.sqrt (2 * s)), Real.exp (-(x ^ 2) * u ^ 2) := by
  have hm : Measurable (fun ω ↦ actualBesselThree T x s ω) := by
    unfold actualBesselThree
    apply Measurable.sqrt
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_const.add (measurable_const.mul
      ((gaussianDyadicPath_measurable _).comp (measurable_pi_apply i)))).pow_const 2
  have hi := (bessel_three_inverse_moment_input_internal.2 T x s hT hx hs hsT).1
  rw [expected_inverse_laplace (independentBridgeLaw (Fin 3)) _ hm
    (bessel_three_positive_input_internal T x s hT hx hs hsT) hi]
  have he (t : ℝ) := bessel_three_quadratic_laplace T x s (t ^ 2) hT hs hsT (sq_nonneg t)
  simp_rw [he]
  rw [radial_laplace_integral_exact s x hs]

end SRWTightness
