import SRWTightness.GaussianPositiveConditioning
import SRWTightness.GaussianMiddleKernelBound

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- The original Gaussian positive-convolution interface is internally proved by scalar
conditioning. -/
theorem gaussian_positive_convolution_input_internal : GaussianPositiveConvolutionInput := by
  intro ν instν v a hv ha
  refine ⟨gaussian_convolution_kernel_integrable ν a v hv, ?_⟩
  have hr := positive_part_sum_three_region_bound (gaussianReal 0 v.toNNReal) ν a ha
  have hk := gaussian_middle_closed_integral_bound ν a v ha.le hv
  exact hr.trans (add_le_add (le_refl _) hk)

end SRWTightness
