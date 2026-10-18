import SRWTightness.WeightedGaussianEnvelope
import SRWTightness.SourceUpperGaussianConvolution

open MeasureTheory Set
namespace SRWTightness

/-- The full generic weighted Gaussian integral input follows internally with a uniform C*h bound.
-/
theorem weighted_gaussian_integral_input_internal : WeightedGaussianIntegralInput := by
  intro c hc
  refine ⟨(1 + Real.sqrt (2 / c)) * Real.sqrt (4 * Real.pi / c), by positivity, ?_⟩
  intro h a hh
  have hh0 : 0 < h := by linarith
  let k := c / (2 * h)
  have hk : 0 < k := div_pos hc (by positivity)
  have hb := weighted_gaussian_interval_bound k a hk
  have hexp : ∀ z : ℝ, -(c * z ^ 2 / (2 * h)) = -k * z ^ 2 := by
    intro z
    dsimp [k]
    ring
  simp_rw [hexp]
  have h₁ : 1 / Real.sqrt k = Real.sqrt (2 / c) * Real.sqrt h := by
    rw [one_div, ← Real.sqrt_inv]
    have hi : k⁻¹ = (2 / c) * h := by
      dsimp [k]
      field_simp [hc.ne', hh0.ne'] <;> ring
    rw [hi, Real.sqrt_mul (by positivity : 0 ≤ (2 / c : ℝ))]
  have h₂ : Real.sqrt (Real.pi / (k / 2)) =
      Real.sqrt (4 * Real.pi / c) * Real.sqrt h := by
    have he : Real.pi / (k / 2) = (4 * Real.pi / c) * h := by
      dsimp [k]
      field_simp [hc.ne', hh0.ne'] <;> ring
    rw [he, Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi / c)]
  have hs : 1 ≤ Real.sqrt h := by simpa using Real.sqrt_le_sqrt hh
  have hcoef : 1 + Real.sqrt (2 / c) * Real.sqrt h ≤
      (1 + Real.sqrt (2 / c)) * Real.sqrt h := by nlinarith
  calc
    _ ≤ (1 + 1 / Real.sqrt k) * Real.sqrt (Real.pi / (k / 2)) := hb
    _ = (1 + Real.sqrt (2 / c) * Real.sqrt h) *
        (Real.sqrt (4 * Real.pi / c) * Real.sqrt h) := by rw [h₁, h₂]
    _ ≤ ((1 + Real.sqrt (2 / c)) * Real.sqrt h) *
        (Real.sqrt (4 * Real.pi / c) * Real.sqrt h) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = ((1 + Real.sqrt (2 / c)) * Real.sqrt (4 * Real.pi / c)) *
        (Real.sqrt h) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hh0.le]

end SRWTightness
