import SRWTightness.ExternalFiniteGaussianBridgeKernel
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- An explicit upper bound for the reflected Gaussian endpoint density. -/
theorem gaussian_reflection_kernel_bound (v q s : ℝ)
    (hv : 0 < v) (hq : 0 ≤ q) (hs : s ≤ q) :
    0 ≤ gaussianPDFReal 0 v.toNNReal s * (1 - Real.exp (-(2 * q * (q - s) / v))) ∧
    gaussianPDFReal 0 v.toNNReal s * (1 - Real.exp (-(2 * q * (q - s) / v))) ≤
      (Real.sqrt (2 * Real.pi * v))⁻¹ * (2 * q * (q - s) / v) := by
  have ha : 0 ≤ 2 * q * (q - s) / v := by positivity
  have hf0 : 0 ≤ 1 - Real.exp (-(2 * q * (q - s) / v)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha))
  have hf1 : 1 - Real.exp (-(2 * q * (q - s) / v)) ≤ 2 * q * (q - s) / v := by
    linarith [Real.add_one_le_exp (-(2 * q * (q - s) / v))]
  have hpdf : gaussianPDFReal 0 v.toNNReal s ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    rw [gaussianPDFReal, Real.coe_toNNReal _ hv.le]
    apply mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  exact ⟨mul_nonneg (gaussianPDFReal_nonneg _ _ _) hf0,
    mul_le_mul hpdf hf1 hf0 (inv_nonneg.mpr (Real.sqrt_nonneg _))⟩

/-- Integrating on an endpoint interval keeps an explicit length factor. -/
theorem gaussian_reflection_kernel_interval_bound (v q a b : ℝ)
    (hv : 0 < v) (hq : 0 ≤ q) (hab : a ≤ b) (hbq : b ≤ q) :
    (∫ s in Set.Icc a b, gaussianPDFReal 0 v.toNNReal s *
      (1 - Real.exp (-(2 * q * (q - s) / v)))) ≤
      ((Real.sqrt (2 * Real.pi * v))⁻¹ * (2 * q * (q - a) / v)) * (b - a) := by
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Set.Icc a b)
    (f := fun s ↦ gaussianPDFReal 0 v.toNNReal s *
      (1 - Real.exp (-(2 * q * (q - s) / v))))
    (C := (Real.sqrt (2 * Real.pi * v))⁻¹ * (2 * q * (q - a) / v))
    isCompact_Icc.measure_lt_top ?_
  · rw [Real.volume_real_Icc_of_le hab] at hnorm
    rw [Real.norm_eq_abs] at hnorm
    exact (le_abs_self _).trans hnorm
  · intro s hs
    have hp := gaussian_reflection_kernel_bound v q s hv hq (hs.2.trans hbq)
    rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
    apply hp.2.trans
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    apply div_le_div_of_nonneg_right _ hv.le
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hs.1 q) (by positivity)

end SRWTightness
