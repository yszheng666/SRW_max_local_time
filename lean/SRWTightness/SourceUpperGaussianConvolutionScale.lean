import SRWTightness.SourceUpperGaussianConvolution

open MeasureTheory Set
namespace SRWTightness

/-- The residual Gaussian cost is uniform when both variance scales are bounded by d. -/
theorem source_upper_gaussian_scaled_cost (c H V d h v q ζ : ℝ)
    (hc : 0 < c) (hH : 0 < H) (hV : 0 < V) (hd : 0 < d)
    (hh : 0 < h) (hv : 0 < v) (hhD : h ≤ H * d) (hvD : v ≤ V * d)
    (hq : 0 ≤ q) (hqζ : q ≤ ζ) :
    (c / (2 * (H + c * V))) * q ^ 2 / d ≤ c * ζ ^ 2 / (2 * (h + c * v)) := by
  have hden : 0 < 2 * (h + c * v) := by positivity
  have hdenD : 2 * (h + c * v) ≤ 2 * ((H + c * V) * d) := by
    nlinarith [mul_le_mul_of_nonneg_left hvD hc.le]
  have hb := div_le_div_of_nonneg_left (mul_nonneg hc.le (sq_nonneg q)) hden hdenD
  have hs : c * q ^ 2 / (2 * (h + c * v)) ≤
      c * ζ ^ 2 / (2 * (h + c * v)) := by
    apply div_le_div_of_nonneg_right _ hden.le
    apply mul_le_mul_of_nonneg_left _ hc.le
    nlinarith
  have he : (c / (2 * (H + c * V))) * q ^ 2 / d =
      c * q ^ 2 / (2 * ((H + c * V) * d)) := by
    field_simp
  rw [he]
  exact hb.trans hs

/-- The terminal convolution has Cd exp(-κq²/d) decay, uniformly in its upper endpoint. -/
theorem source_upper_gaussian_scaled_convolution (hIntegral : WeightedGaussianIntegralInput)
    (c H V : ℝ) (hc : 0 < c) (hH : 0 < H) (hV : 0 < V) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a d h v q ζ : ℝ,
      0 < d → 1 ≤ h → 0 < v → h ≤ H * d → v ≤ V * d → 0 ≤ q → q ≤ ζ →
      (∫ z in Icc 0 a, (1 + z) *
        Real.exp (-((ζ - z) ^ 2 / (2 * v) + c * z ^ 2 / h))) ≤
      C * d * Real.exp (-(κ * q ^ 2 / d)) := by
  obtain ⟨C, hC, hbound⟩ := source_upper_gaussian_convolution_bound hIntegral c hc
  refine ⟨C * H, c / (2 * (H + c * V)), by positivity, by positivity, ?_⟩
  intro a d h v q ζ hd hh hv hhD hvD hq hqζ
  have hcost := source_upper_gaussian_scaled_cost c H V d h v q ζ hc hH hV hd
    (by linarith) hv hhD hvD hq hqζ
  have he := Real.exp_le_exp.mpr (neg_le_neg hcost)
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hhD hC.le) he
    (Real.exp_nonneg _) (by positivity : 0 ≤ C * (H * d))
  exact (hbound a ζ v h hv hh).trans (by simpa only [mul_assoc] using hm)

end SRWTightness
