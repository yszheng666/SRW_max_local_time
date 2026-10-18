import SRWTightness.SourceUpperGaussianSquares
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
namespace SRWTightness

/-- A generic one-dimensional Gaussian integral bound, independent of the SRW model. -/
def WeightedGaussianIntegralInput : Prop :=
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ h a : ℝ, 1 ≤ h →
    (∫ z in Icc 0 a, (1 + z) * Real.exp (-(c * z ^ 2 / (2 * h)))) ≤ C * h

/-- The upper-block convolution is bounded by a Gaussian integral with a separated height cost. -/
theorem source_upper_gaussian_convolution_envelope (a ζ v h c : ℝ)
    (hv : 0 < v) (hh : 0 < h) (hc : 0 < c) :
    (∫ z in Icc 0 a, (1 + z) *
      Real.exp (-((ζ - z) ^ 2 / (2 * v) + c * z ^ 2 / h))) ≤
    Real.exp (-(c * ζ ^ 2 / (2 * (h + c * v)))) *
      ∫ z in Icc 0 a, (1 + z) * Real.exp (-(c * z ^ 2 / (2 * h))) := by
  rw [← integral_const_mul]
  apply setIntegral_mono_on
    (show Continuous (fun z : ℝ ↦ (1 + z) *
      Real.exp (-((ζ - z) ^ 2 / (2 * v) + c * z ^ 2 / h))) by
        fun_prop).continuousOn.integrableOn_Icc
    (show Continuous (fun z : ℝ ↦ Real.exp (-(c * ζ ^ 2 / (2 * (h + c * v)))) *
      ((1 + z) * Real.exp (-(c * z ^ 2 / (2 * h))))) by fun_prop).continuousOn.integrableOn_Icc
    measurableSet_Icc
  intro z hz
  have hb := mul_le_mul_of_nonneg_left
    (source_upper_gaussian_exponential_bound ζ z v h c hv hh hc)
    (show 0 ≤ 1 + z by linarith [hz.1])
  simpa only [mul_left_comm (1 + z)] using hb

/-- Uniform convolution bound; its only analytic input is the generic weighted integral. -/
theorem source_upper_gaussian_convolution_bound (hIntegral : WeightedGaussianIntegralInput)
    (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ζ v h : ℝ, 0 < v → 1 ≤ h →
      (∫ z in Icc 0 a, (1 + z) *
        Real.exp (-((ζ - z) ^ 2 / (2 * v) + c * z ^ 2 / h))) ≤
      C * h * Real.exp (-(c * ζ ^ 2 / (2 * (h + c * v)))) := by
  obtain ⟨C, hC, hI⟩ := hIntegral c hc
  refine ⟨C, hC, ?_⟩
  intro a ζ v h hv hh
  have hb := source_upper_gaussian_convolution_envelope a ζ v h c hv (by linarith) hc
  have hi := mul_le_mul_of_nonneg_left (hI h a hh)
    (Real.exp_nonneg (-(c * ζ ^ 2 / (2 * (h + c * v)))))
  exact hb.trans (by simpa only [mul_comm _ (C * h)] using hi)

/-- Restore the leading exponential from source (4.9) before estimating the convolution. -/
theorem source_upper_gaussian_convolution_factor (a v h c : ℝ) (hv : 0 < v) :
    (∫ z in Icc 0 a, (1 + z) *
      Real.exp (-(a - z) ^ 2 / (2 * v) - 2 * z - c * z ^ 2 / h)) =
    Real.exp (-2 * a + 2 * v) *
      ∫ z in Icc 0 a, (1 + z) *
        Real.exp (-((a - 2 * v - z) ^ 2 / (2 * v) + c * z ^ 2 / h)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [source_upper_gaussian_linear_square a z v hv]
  have he : -2 * a + 2 * v - (a - 2 * v - z) ^ 2 / (2 * v) - c * z ^ 2 / h =
      (-2 * a + 2 * v) + -((a - 2 * v - z) ^ 2 / (2 * v) + c * z ^ 2 / h) := by ring
  rw [he, Real.exp_add]
  ring

end SRWTightness
