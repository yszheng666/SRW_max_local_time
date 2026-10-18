import SRWTightness.GaussianConvolutionKernel

open MeasureTheory ProbabilityTheory Set Filter
namespace SRWTightness

/-- A nondegenerate Gaussian set integral is exactly the corresponding density-weighted integral. -/
theorem gaussian_real_set_integral_density (f : ℝ → ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) (v : ℝ) (hv : 0 < v) :
    (∫ x in s, f x ∂gaussianReal 0 v.toNNReal) =
      ∫ x in s, gaussianPDFReal 0 v.toNNReal x * f x := by
  have hv₀ : v.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hv)
  rw [← integral_indicator hs, integral_gaussianReal_eq_integral_smul hv₀]
  have hp : ∀ x : ℝ, gaussianPDFReal 0 v.toNNReal x * s.indicator f x =
      s.indicator (fun y ↦ gaussianPDFReal 0 v.toNNReal y * f y) x := by
    intro x
    by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero]
  simp_rw [smul_eq_mul, hp]
  rw [integral_indicator hs]

/-- The actual Gaussian middle interval is controlled by the literal reflected convolution kernel.
-/
theorem gaussian_middle_closed_integral_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a v : ℝ) (ha : 0 ≤ a) (hv : 0 < v) :
    (∫ x in Icc 0 a, ν.real (Ici (a - x)) ∂gaussianReal 0 v.toNNReal) ≤
      (1 / Real.sqrt v) * (∫ z in Icc 0 a, ν.real (Ici z) *
        Real.exp (-((a - z) ^ 2 / (2 * v)))) := by
  let f : ℝ → ℝ := fun x ↦ ν.real (Ici (a - x))
  have mf : Measurable f :=
    (probability_closed_tail_measurable ν).comp (measurable_const.sub measurable_id)
  have mp : Measurable (fun x : ℝ ↦ f x * Real.exp (-(x ^ 2 / (2 * v)))) :=
    mf.mul (by fun_prop)
  have hp : IntegrableOn (fun x : ℝ ↦ f x * Real.exp (-(x ^ 2 / (2 * v))))
      (Icc 0 a) volume := by
    apply (integrable_const (1 : ℝ) (μ := volume.restrict (Icc 0 a))).mono'
      mp.aestronglyMeasurable
    filter_upwards [] with x
    have hn : 0 ≤ f x * Real.exp (-(x ^ 2 / (2 * v))) :=
      mul_nonneg measureReal_nonneg (Real.exp_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    have he : Real.exp (-(x ^ 2 / (2 * v))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by positivity)))
    have hb := mul_le_mul (measureReal_le_one (μ := ν) (s := Ici (a - x))) he
      (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [f, mul_one] using hb
  have hright := hp.const_mul (1 / Real.sqrt v)
  have hpoint : ∀ x : ℝ, gaussianPDFReal 0 v.toNNReal x * f x ≤
      (1 / Real.sqrt v) * (f x * Real.exp (-(x ^ 2 / (2 * v)))) := by
    intro x
    have hm := mul_le_mul_of_nonneg_right (gaussian_real_density_kernel_bound v hv x)
      (measureReal_nonneg (μ := ν) (s := Ici (a - x)))
    simpa only [f, mul_assoc, mul_comm, mul_left_comm] using hm
  have mleft : Measurable (fun x : ℝ ↦ gaussianPDFReal 0 v.toNNReal x * f x) :=
    (by fun_prop : Measurable (gaussianPDFReal 0 v.toNNReal)).mul mf
  have hleft : IntegrableOn (fun x : ℝ ↦ gaussianPDFReal 0 v.toNNReal x * f x)
      (Icc 0 a) volume := by
    apply hright.mono' mleft.aestronglyMeasurable
    filter_upwards [] with x
    have hn : 0 ≤ gaussianPDFReal 0 v.toNNReal x * f x :=
      mul_nonneg (gaussianPDFReal_nonneg _ _ _) measureReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact hpoint x
  have hbound := setIntegral_mono_on hleft hright measurableSet_Icc (fun x _ ↦ hpoint x)
  rw [integral_const_mul] at hbound
  have hreflect : (∫ x in Icc 0 a, f x * Real.exp (-(x ^ 2 / (2 * v)))) =
      ∫ z in Icc 0 a, ν.real (Ici z) * Real.exp (-((a - z) ^ 2 / (2 * v))) := by
    have hr := closed_interval_integral_reflection
      (fun z : ℝ ↦ ν.real (Ici z) * Real.exp (-((a - z) ^ 2 / (2 * v)))) a ha
    have he : ∀ x : ℝ, a - (a - x) = x := fun x ↦ by ring
    simpa only [f, he] using hr
  rw [hreflect] at hbound
  rw [gaussian_real_set_integral_density _ (Icc 0 a) measurableSet_Icc v hv]
  exact hbound

end SRWTightness
