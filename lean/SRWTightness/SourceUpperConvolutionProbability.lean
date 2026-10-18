import SRWTightness.ExternalGaussianConvolution
import SRWTightness.SourceUpperTerminalConvolution

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- A residual tail bound is integrated against the actual Gaussian kernel on [0,a]. -/
theorem source_upper_convolution_probability (hConv : GaussianPositiveConvolutionInput)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (a v h c D : ℝ)
    (ha : 0 < a) (hv : 0 < v)
    (hTail : ∀ z : ℝ, 0 ≤ z →
      ν.real (Ici z) ≤ D * (1 + z) * Real.exp (-2 * z - c * z ^ 2 / h)) :
    ((gaussianReal 0 v.toNNReal).prod ν).real {p | a ≤ max p.1 0 + p.2} ≤
      (gaussianReal 0 v.toNNReal).real (Ici a) +
      D * ((1 + a) * Real.exp (-2 * a - c * a ^ 2 / h)) +
      D * ((1 / Real.sqrt v) * (∫ z in Icc 0 a, (1 + z) *
        Real.exp (-(a - z) ^ 2 / (2 * v) - 2 * z - c * z ^ 2 / h))) := by
  obtain ⟨hi, hp⟩ := hConv ν v a hv ha
  have hb : (∫ z in Icc 0 a, ν.real (Ici z) *
      Real.exp (-((a - z) ^ 2 / (2 * v)))) ≤
      D * ∫ z in Icc 0 a, (1 + z) *
        Real.exp (-(a - z) ^ 2 / (2 * v) - 2 * z - c * z ^ 2 / h) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hi
      (show Continuous (fun z : ℝ ↦ D * ((1 + z) *
        Real.exp (-(a - z) ^ 2 / (2 * v) - 2 * z - c * z ^ 2 / h))) by
          fun_prop).continuousOn.integrableOn_Icc measurableSet_Icc
    intro z hz
    have ht := mul_le_mul_of_nonneg_right (hTail z hz.1)
      (Real.exp_nonneg (-((a - z) ^ 2 / (2 * v))))
    have he : Real.exp (-2 * z - c * z ^ 2 / h) *
        Real.exp (-((a - z) ^ 2 / (2 * v))) =
        Real.exp (-(a - z) ^ 2 / (2 * v) - 2 * z - c * z ^ 2 / h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simpa only [mul_assoc, he] using ht
  have hInt := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1 / Real.sqrt v)
  have hEnd := hTail a ha.le
  have hsum := add_le_add (add_le_add_left hEnd
    ((gaussianReal 0 v.toNNReal).real (Ici a))) hInt
  exact hp.trans (by convert hsum using 1 <;> ring)

end SRWTightness
