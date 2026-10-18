import SRWTightness.SourceUpperGaussianConvolutionScale

open MeasureTheory Set
namespace SRWTightness

/-- The convolution bound retains its Gaussian decay for either sign of the residual height. -/
theorem source_upper_gaussian_all_height_convolution
    (hIntegral : WeightedGaussianIntegralInput) (c H V : ℝ)
    (hc : 0 < c) (hH : 0 < H) (hV : 0 < V) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a d h v ζ : ℝ,
      0 < d → 1 ≤ h → 0 < v → h ≤ H * d → v ≤ V * d →
      (∫ z in Icc 0 a, (1 + z) *
        Real.exp (-((ζ - z) ^ 2 / (2 * v) + c * z ^ 2 / h))) ≤
      C * d * Real.exp (-(κ * ζ ^ 2 / d)) := by
  obtain ⟨C, hC, hbound⟩ := source_upper_gaussian_convolution_bound hIntegral c hc
  refine ⟨C * H, c / (2 * (H + c * V)), by positivity, by positivity, ?_⟩
  intro a d h v ζ hd hh hv hhD hvD
  have hcost := source_upper_gaussian_scaled_cost c H V d h v |ζ| |ζ| hc hH hV hd
    (by linarith) hv hhD hvD (abs_nonneg _) le_rfl
  simp only [sq_abs] at hcost
  have he := Real.exp_le_exp.mpr (neg_le_neg hcost)
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hhD hC.le) he
    (Real.exp_nonneg _) (by positivity : 0 ≤ C * (H * d))
  exact (hbound a ζ v h hv hh).trans (by simpa only [mul_assoc] using hm)

/-- A bounded downward error loses only a fixed fraction of positive-height square decay. -/
theorem source_upper_gaussian_shift_square (q ζ E : ℝ) (hE : 0 ≤ E)
    (hshift : q - E ≤ ζ) : (max q 0) ^ 2 / 2 - E ^ 2 ≤ ζ ^ 2 := by
  by_cases hq : 0 ≤ q
  · rw [max_eq_left hq]
    have hz : 0 ≤ ζ + E := by linarith
    have hs : q ^ 2 ≤ (ζ + E) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (ζ - E)]
  · rw [max_eq_right (le_of_not_ge hq)]
    nlinarith [sq_nonneg ζ, sq_nonneg E]

/-- A bounded shift changes only the uniform constant and the quadratic decay coefficient. -/
theorem source_upper_gaussian_shift_exponential (q ζ E κ d : ℝ)
    (hE : 0 ≤ E) (hκ : 0 < κ) (hd : 1 ≤ d) (hshift : q - E ≤ ζ) :
    Real.exp (-(κ * ζ ^ 2 / d)) ≤
      Real.exp (κ * E ^ 2) * Real.exp (-((κ / 2) * (max q 0) ^ 2 / d)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := source_upper_gaussian_shift_square q ζ E hE hshift
  have hsd := mul_le_mul_of_nonneg_left hs hκ.le
  have hEd := mul_le_mul_of_nonneg_left hd (mul_nonneg hκ.le (sq_nonneg E))
  have hd0 : 0 < d := by linarith
  apply (mul_le_mul_iff_left₀ hd0).mp
  field_simp
  have hEd0 := mul_le_mul_of_nonneg_left hd (sq_nonneg E)
  nlinarith only [hs, hEd0]

/-- Uniform terminal convolution decay in the source positive height, with bounded errors. -/
theorem source_upper_gaussian_shifted_convolution
    (hIntegral : WeightedGaussianIntegralInput) (c H V E : ℝ)
    (hc : 0 < c) (hH : 0 < H) (hV : 0 < V) (hE : 0 ≤ E) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a d h v q ζ : ℝ,
      1 ≤ d → 1 ≤ h → 0 < v → h ≤ H * d → v ≤ V * d → q - E ≤ ζ →
      (∫ z in Icc 0 a, (1 + z) *
        Real.exp (-((ζ - z) ^ 2 / (2 * v) + c * z ^ 2 / h))) ≤
      C * d * Real.exp (-(κ * (max q 0) ^ 2 / d)) := by
  obtain ⟨C, κ, hC, hκ, hbound⟩ :=
    source_upper_gaussian_all_height_convolution hIntegral c H V hc hH hV
  refine ⟨C * Real.exp (κ * E ^ 2), κ / 2, by positivity, by positivity, ?_⟩
  intro a d h v q ζ hd hh hv hhD hvD hshift
  have he := source_upper_gaussian_shift_exponential q ζ E κ d hE hκ hd hshift
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ C * d)
  exact (hbound a d h v ζ (by linarith) hh hv hhD hvD).trans (by
    convert hm using 1 <;> ring)

end SRWTightness
