import SRWTightness.GaussianConvolutionKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- A centered Gaussian exponent is bounded by its exact tangent exponential at the threshold. -/
theorem gaussian_quadratic_tangent_envelope (v a x : ℝ) (hv : 0 < v) :
    Real.exp (-(x ^ 2 / (2 * v))) ≤
      Real.exp (-(a ^ 2 / (2 * v))) * Real.exp (-(a / v) * (x - a)) := by
  have he : -(a ^ 2 / (2 * v)) - (a / v) * (x - a) - (-(x ^ 2 / (2 * v))) =
      (x - a) ^ 2 / (2 * v) := by
    field_simp [hv.ne'] <;> ring
  have hc : -(x ^ 2 / (2 * v)) ≤ -(a ^ 2 / (2 * v)) - (a / v) * (x - a) := by
    have hp := div_nonneg (sq_nonneg (x - a)) (by positivity : 0 ≤ 2 * v)
    linarith
  have hp := Real.exp_le_exp.mpr hc
  have hf : -(a ^ 2 / (2 * v)) - (a / v) * (x - a) =
      -(a ^ 2 / (2 * v)) + (-(a / v) * (x - a)) := by ring
  rw [hf, Real.exp_add] at hp
  exact hp

/-- The tangent exponential has the exact closed half-line integral v/a. -/
theorem gaussian_tangent_tail_integral (v a : ℝ) (hv : 0 < v) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-(a / v) * (x - a))) (Ici a) volume ∧
      (∫ x in Ici a, Real.exp (-(a / v) * (x - a))) = v / a := by
  let k := a / v
  have hk : 0 < k := div_pos ha hv
  have hneg : -k < 0 := by linarith
  have hshift : ∀ x : ℝ, Real.exp (-k * (x - a)) =
      Real.exp (k * a) * Real.exp (-k * x) := by
    intro x
    rw [← Real.exp_add]
    congr 1
    ring
  have hi := (integrableOn_exp_mul_Ioi hneg a).const_mul (Real.exp (k * a))
  have hclosed : IntegrableOn (fun x : ℝ ↦ Real.exp (-k * (x - a))) (Ici a) volume := by
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    change Integrable (fun x : ℝ ↦ Real.exp (-k * (x - a))) (volume.restrict (Ioi a))
    simp_rw [hshift]
    exact hi
  refine ⟨hclosed, ?_⟩
  change (∫ x in Ici a, Real.exp (-k * (x - a))) = v / a
  simp_rw [hshift]
  rw [integral_const_mul, integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi hneg a]
  have hc : Real.exp (k * a) * Real.exp (-k * a) = 1 := by
    rw [← Real.exp_add, show k * a + -k * a = 0 by ring, Real.exp_zero]
  calc
    _ = (Real.exp (k * a) * Real.exp (-k * a)) / k := by
      field_simp [hk.ne'] <;> ring
    _ = 1 / k := by rw [hc]
    _ = v / a := by dsimp [k]; field_simp [hv.ne', ha.ne']

end SRWTightness
