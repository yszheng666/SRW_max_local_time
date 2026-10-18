import SRWTightness.ExternalGaussianConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory ProbabilityTheory Set Filter
namespace SRWTightness

/-- Closed real tails are measurable even when the probability measure has atoms. -/
theorem probability_closed_tail_measurable (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measurable (fun z : ℝ ↦ ν.real (Ici z)) := by
  have ha : Antitone (fun z : ℝ ↦ ν.real (Ici z)) := by
    intro x y hxy
    apply measureReal_mono (h₂ := measure_ne_top ν _)
    intro z hz
    exact hxy.trans hz
  exact ha.measurable

/-- The original Gaussian convolution kernel is integrable on every finite closed interval. -/
theorem gaussian_convolution_kernel_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a v : ℝ) (hv : 0 < v) :
    IntegrableOn (fun z ↦ ν.real (Ici z) * Real.exp (-((a - z) ^ 2 / (2 * v))))
      (Icc 0 a) volume := by
  have hm : Measurable (fun z : ℝ ↦ ν.real (Ici z) *
      Real.exp (-((a - z) ^ 2 / (2 * v)))) :=
    (probability_closed_tail_measurable ν).mul (by fun_prop)
  apply (integrable_const (1 : ℝ) (μ := volume.restrict (Icc 0 a))).mono'
    hm.aestronglyMeasurable
  filter_upwards [] with z
  have hp : 0 ≤ ν.real (Ici z) * Real.exp (-((a - z) ^ 2 / (2 * v))) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hp]
  have he : Real.exp (-((a - z) ^ 2 / (2 * v))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by positivity)))
  have hb := mul_le_mul (measureReal_le_one (μ := ν) (s := Ici z)) he
    (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [mul_one] using hb

/-- The actual centered Gaussian density is bounded by the source's unnormalized kernel. -/
theorem gaussian_real_density_kernel_bound (v : ℝ) (hv : 0 < v) (x : ℝ) :
    gaussianPDFReal 0 v.toNNReal x ≤
      (1 / Real.sqrt v) * Real.exp (-(x ^ 2 / (2 * v))) := by
  rw [gaussianPDFReal, Real.coe_toNNReal _ hv.le, sub_zero]
  have hscale : v ≤ 2 * Real.pi * v := by
    have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [mul_nonneg (sub_nonneg.mpr hπ) hv.le]
  have hs := Real.sqrt_le_sqrt hscale
  have hi := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hv) hs
  have hb := mul_le_mul_of_nonneg_right hi (Real.exp_nonneg (-(x ^ 2 / (2 * v))))
  simpa only [one_div, neg_div] using hb

/-- Reflecting a closed finite interval preserves its Lebesgue integral. -/
theorem closed_interval_integral_reflection (f : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in Icc 0 a, f (a - x)) = ∫ x in Icc 0 a, f x := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha,
    intervalIntegral.integral_comp_sub_left f a]
  simp only [sub_self, sub_zero]
  rw [intervalIntegral.integral_of_le ha, ← integral_Icc_eq_integral_Ioc]

end SRWTightness
