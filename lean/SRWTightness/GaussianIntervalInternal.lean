import SRWTightness.SourceGaussianEndpointWindow
import SRWTightness.GaussianReflectionKernelBound

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Explicit density constants on every bounded standardized interval. -/
theorem gaussian_density_standardized_bounds (R v x : ℝ) (hR : 0 ≤ R) (hv : 0 < v)
    (hx : |x| ≤ R * Real.sqrt v) :
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(R ^ 2 / 2)) / Real.sqrt v ≤
      gaussianPDFReal 0 v.toNNReal x ∧
    gaussianPDFReal 0 v.toNNReal x ≤ (Real.sqrt (2 * Real.pi))⁻¹ / Real.sqrt v := by
  have hs : x ^ 2 ≤ R ^ 2 * v := by
    have hh := (sq_le_sq₀ (abs_nonneg x) (by positivity)).mpr hx
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hv.le] using hh
  have he : Real.exp (-(R ^ 2 / 2)) ≤ Real.exp (-(x ^ 2) / (2 * v)) := by
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hu : Real.exp (-(x ^ 2) / (2 * v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg x)) (by positivity))
  rw [gaussianPDFReal, Real.coe_toNNReal _ hv.le, sub_zero,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  constructor
  · have hh := mul_le_mul_of_nonneg_left he
      (inv_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg (2 * Real.pi)) (Real.sqrt_nonneg v)))
    simpa only [mul_inv_rev, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left hu
      (inv_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg (2 * Real.pi)) (Real.sqrt_nonneg v)))
    simpa only [mul_inv_rev, mul_one, one_mul, div_eq_mul_inv, mul_comm] using hh

/-- The entire original bounded-standardized Gaussian interval input is internal. -/
theorem gaussian_interval_input_internal : GaussianIntervalInput := by
  intro R hR
  let C := (Real.sqrt (2 * Real.pi))⁻¹
  let c := C * Real.exp (-(R ^ 2 / 2))
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := mul_pos hC (Real.exp_pos _)
  refine ⟨c, C, hc, hC, ?_⟩
  intro v l u hv hlu hl hu
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc l u) :
      c / Real.sqrt v ≤ gaussianPDFReal 0 v.toNNReal x ∧
        gaussianPDFReal 0 v.toNNReal x ≤ C / Real.sqrt v := by
    apply gaussian_density_standardized_bounds R v x hR hv
    rw [abs_le]
    constructor
    · linarith [(abs_le.mp hl).1, hx.1]
    · linarith [(abs_le.mp hu).2, hx.2]
  have hi : IntegrableOn (gaussianPDFReal 0 v.toNNReal) (Set.Icc l u) volume :=
    (integrable_gaussianPDFReal 0 v.toNNReal).integrableOn
  have hlo := setIntegral_mono_on (integrable_const (c / Real.sqrt v)) hi
    measurableSet_Icc (fun x hx ↦ (hpoint x hx).1)
  have hhi := setIntegral_mono_on hi (integrable_const (C / Real.sqrt v))
    measurableSet_Icc (fun x hx ↦ (hpoint x hx).2)
  have he : (gaussianReal 0 v.toNNReal).real (Set.Icc l u) =
      ∫ x in Set.Icc l u, gaussianPDFReal 0 v.toNNReal x := by
    rw [Measure.real, gaussianReal_apply_eq_integral 0
      (ne_of_gt (Real.toNNReal_pos.mpr hv)), ENNReal.toReal_ofReal]
    exact integral_nonneg (gaussianPDFReal_nonneg _ _)
  rw [he]
  simp only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] at hlo hhi
  rw [← Measure.real, Real.volume_real_Icc_of_le hlu] at hlo hhi
  constructor
  · simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hlo
  · simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hhi

end SRWTightness
