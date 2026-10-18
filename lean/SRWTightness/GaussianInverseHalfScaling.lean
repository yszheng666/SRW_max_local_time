import SRWTightness.GaussianAbsoluteNegativeMoment
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory

open scoped NNReal

namespace SRWTightness

/-- Positive-variance centered Gaussians are the exact scaled standard Gaussian law. -/
theorem gaussian_standard_positive_scaling (s : ℝ) (hs : 0 < s) :
    HasLaw (fun z : ℝ ↦ Real.sqrt s * z) (gaussianReal 0 s.toNNReal) (gaussianReal 0 1) := by
  have hv : (⟨(Real.sqrt s) ^ 2, sq_nonneg _⟩ : ℝ≥0) = s.toNNReal := by
    apply Subtype.ext
    change (Real.sqrt s) ^ 2 = max s 0
    rw [Real.sq_sqrt hs.le, max_eq_left hs.le]
  refine ⟨by fun_prop, ?_⟩
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  exact congrArg (gaussianReal 0) hv

/-- The absolute inverse-half moment has exact square-root scaling and is integrable. -/
theorem gaussian_inverse_half_scaling (s : ℝ) (hs : 0 < s) :
    Integrable (fun z : ℝ ↦ |z| ^ (-(1 / 2 : ℝ))) (gaussianReal 0 s.toNNReal) ∧
    (∫ z : ℝ, |z| ^ (-(1 / 2 : ℝ)) ∂gaussianReal 0 s.toNNReal) =
      (Real.sqrt s) ^ (-(1 / 2 : ℝ)) *
        (∫ z : ℝ, |z| ^ (-(1 / 2 : ℝ)) ∂gaussianReal 0 1) := by
  have hf : Measurable (fun z : ℝ ↦ |z| ^ (-(1 / 2 : ℝ))) := by fun_prop
  have hlaw := gaussian_standard_positive_scaling s hs
  have hp := hlaw.measurePreserving (by fun_prop)
  have he (z : ℝ) : |Real.sqrt s * z| ^ (-(1 / 2 : ℝ)) =
      (Real.sqrt s) ^ (-(1 / 2 : ℝ)) * |z| ^ (-(1 / 2 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg s),
      Real.mul_rpow (Real.sqrt_nonneg s) (abs_nonneg z)]
  have hi : Integrable
      ((fun z : ℝ ↦ |z| ^ (-(1 / 2 : ℝ))) ∘ (fun z : ℝ ↦ Real.sqrt s * z))
      (gaussianReal 0 1) := by
    simpa only [Function.comp_def, he] using
      gaussian_standard_inverse_half_integrable.const_mul ((Real.sqrt s) ^ (-(1 / 2 : ℝ)))
  refine ⟨(hp.integrable_comp hf.aestronglyMeasurable).mp hi, ?_⟩
  have hh := hlaw.integral_comp hf.aestronglyMeasurable
  simp only [Function.comp_def, he] at hh
  rw [integral_const_mul] at hh
  exact hh.symm

end SRWTightness
