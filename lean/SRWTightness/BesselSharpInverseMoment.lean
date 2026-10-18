import SRWTightness.ExpectedInverseLaplace
import SRWTightness.BesselQuadraticLaplace
import SRWTightness.RadialLaplaceSubstitution
import SRWTightness.BesselInverseMomentInternal
import SRWTightness.BesselThreePositiveInternal

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual three-dimensional radial inverse moment is bounded by the initial inverse radius. -/
theorem bessel_three_sharp_inverse_moment (T x s : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hs : 0 < s) (hsT : s ≤ T) :
    (∫ ω, (actualBesselThree T x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)) ≤ x⁻¹ := by
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
  have hb := mul_le_mul_of_nonneg_left (radial_laplace_integral_bound s x hs.le hx)
    (by positivity : 0 ≤ 2 / Real.sqrt Real.pi)
  apply hb.trans_eq
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp

end SRWTightness
