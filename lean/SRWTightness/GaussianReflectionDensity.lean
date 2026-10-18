import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

open ProbabilityTheory
namespace SRWTightness

/-- Reflection weights a centered Gaussian density into its reflected density. -/
theorem gaussian_reflection_density (s q b : ℝ) (hs : 0 < s) :
    gaussianPDFReal 0 s.toNNReal b * Real.exp (-(2 * q * (q - b) / s)) =
      gaussianPDFReal 0 s.toNNReal (2 * q - b) := by
  simp only [gaussianPDFReal_def, Real.coe_toNNReal s hs.le, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  field_simp [ne_of_gt hs]
  <;> ring

end SRWTightness
