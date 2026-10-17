import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- A standard one-dimensional Mills bound, with the harmless normalizing constant omitted. -/
def GaussianMillsInput : Prop :=
  ∀ v a : ℝ, 0 < v → 0 < a →
    (gaussianReal 0 v.toNNReal).real (Ici a) ≤
      Real.sqrt v / a * Real.exp (-a ^ 2 / (2 * v))

/-- At a threshold at least the variance, Mills supplies the inverse-square-root prefactor. -/
theorem gaussian_mills_variance_threshold (hMills : GaussianMillsInput)
    (v a : ℝ) (hv : 0 < v) (ha : v ≤ a) :
    (gaussianReal 0 v.toNNReal).real (Ici a) ≤
      (1 / Real.sqrt v) * Real.exp (-a ^ 2 / (2 * v)) := by
  have ha0 : 0 < a := hv.trans_le ha
  have hs : Real.sqrt v / a ≤ 1 / Real.sqrt v := by
    rw [div_le_div_iff₀ ha0 (Real.sqrt_pos.2 hv)]
    simpa only [Real.mul_self_sqrt hv.le, one_mul] using ha
  exact (hMills v a hv ha0).trans
    (mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _))

end SRWTightness
