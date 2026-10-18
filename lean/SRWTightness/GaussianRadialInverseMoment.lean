import SRWTightness.GaussianRadialPositive
import SRWTightness.InverseIntegrableOfLaplace
import SRWTightness.RadialLaplaceIntegrable

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Gaussian radial convolution decreases the inverse radius in dimension three. -/
theorem gaussian_three_radial_inverse_moment (m : Fin 3 → ℝ) (s : ℝ) (hs : 0 < s)
    (hm : 0 < ∑ i, (m i) ^ 2) :
    Integrable (fun z : Fin 3 → ℝ ↦ (Real.sqrt (∑ i, (z i) ^ 2))⁻¹)
      (Measure.pi (fun i ↦ gaussianReal (m i) s.toNNReal)) ∧
      (∫ z : Fin 3 → ℝ, (Real.sqrt (∑ i, (z i) ^ 2))⁻¹
        ∂Measure.pi (fun i ↦ gaussianReal (m i) s.toNNReal)) ≤
          (Real.sqrt (∑ i, (m i) ^ 2))⁻¹ := by
  let μ := Measure.pi (fun i ↦ gaussianReal (m i) s.toNNReal)
  let R : (Fin 3 → ℝ) → ℝ := fun z ↦ Real.sqrt (∑ i, (z i) ^ 2)
  let x := Real.sqrt (∑ i, (m i) ^ 2)
  have hx : 0 < x := Real.sqrt_pos.mpr hm
  have hsq : x ^ 2 = ∑ i, (m i) ^ 2 := Real.sq_sqrt hm.le
  have hR : Measurable R := by
    exact (Finset.measurable_sum _ (fun i _ ↦ (measurable_pi_apply i).pow_const 2)).sqrt
  have hp : ∀ᵐ z ∂μ, 0 < R z := gaussian_three_radial_positive m s hs
  have he (t : ℝ) : (∫ z, Real.exp (-(t ^ 2) * (R z) ^ 2) ∂μ) =
      Real.exp (-(t ^ 2) * x ^ 2 / (1 + 2 * s * t ^ 2)) /
        (Real.sqrt (1 + 2 * s * t ^ 2)) ^ 3 := by
    simp only [R, Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)), μ]
    rw [gaussian_vector_quadratic_laplace m s (t ^ 2) hs (sq_nonneg t), hsq]
    rfl
  have hil : IntegrableOn (fun t : ℝ ↦ ∫ z, Real.exp (-(t ^ 2) * (R z) ^ 2) ∂μ)
      (Set.Ioi 0) := by
    simpa only [he] using radial_laplace_integrable s x hs.le hx
  have hi := inverse_integrable_of_laplace μ R hR hp hil
  refine ⟨hi, ?_⟩
  rw [expected_inverse_laplace μ R hR hp hi]
  simp_rw [he]
  have hb := mul_le_mul_of_nonneg_left (radial_laplace_integral_bound s x hs.le hx)
    (by positivity : 0 ≤ 2 / Real.sqrt Real.pi)
  apply hb.trans_eq
  have hπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  change (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / (2 * x)) = x⁻¹
  field_simp

end SRWTightness
