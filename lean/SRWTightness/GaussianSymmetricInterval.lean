import SRWTightness.EvenIntervalIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The centered Gaussian mass of a symmetric interval equals twice its positive
density integral. -/
theorem gaussian_symmetric_interval (s x : ℝ) (hs : 0 < s) (hx : 0 ≤ x) :
    (gaussianReal 0 s.toNNReal).real (Set.Icc (-x) x) =
      2 * (Real.sqrt (2 * Real.pi * s))⁻¹ *
        ∫ t in 0..x, Real.exp (-(t ^ 2) / (2 * s)) := by
  have hv : s.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hs)
  have hc : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs.le
  have hcont : Continuous (fun t : ℝ ↦ Real.exp (-(t ^ 2) / (2 * s))) := by
    fun_prop
  change (gaussianReal 0 s.toNNReal (Set.Icc (-x) x)).toReal = _
  rw [gaussianReal_apply_eq_integral 0 hv, ENNReal.toReal_ofReal
    (integral_nonneg (fun t ↦ gaussianPDFReal_nonneg 0 s.toNNReal t))]
  simp only [gaussianPDFReal_def, hc, sub_zero]
  rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -x ≤ x)]
  rw [even_interval_integral _ hcont (fun t ↦ by simp) x]
  ring

end SRWTightness
