import SRWTightness.MarkSumGenerating
import Mathlib.Probability.Distributions.Poisson.Basic

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

 theorem poisson_power_integral (r : ℝ≥0) (c : ℝ) :
    (∫ k : ℕ, c ^ k ∂poissonMeasure r) = Real.exp ((r : ℝ) * (c - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  have ht (k : ℕ) : Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ) * c ^ k =
      Real.exp (-(r : ℝ)) * (((r : ℝ) * c) ^ k / (k.factorial : ℝ)) := by
    rw [mul_pow]
    ring
  simp_rw [ht]
  rw [tsum_mul_left, (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * c)).tsum_eq,
    ← Real.exp_eq_exp_ℝ, ← Real.exp_add]
  congr 1
  ring

/-- Poissonizing the actual finite product of reference marks gives the exponential resolvent.
The outer expectation selects the count; the inner one samples that many independent marks. -/
theorem poissonized_marks_generating (D A : Finset Site) (hAD : A ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (r : ℝ≥0)
    (v : A → ℝ) (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) :
    (∫ k : ℕ, (∫ Y, markMonomial v (sumMarks A k Y) ∂markProductLaw D A α k)
      ∂poissonMeasure r) =
      Real.exp ((r : ℝ) * α *
        ∑ z : A, (v z - 1) * ((observationResolventMatrix D A v)⁻¹.mulVec 1) z) := by
  simp_rw [markSum_generating_unit_cube D A hAD α hα hcap _ v hv0 hv1]
  rw [poisson_power_integral]
  congr 1
  ring

end SRWTightness
