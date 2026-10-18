import SRWTightness.NormalizedIncrementMoment

open MeasureTheory

namespace SRWTightness

/-- Uniform coordinate second moments control their nonnegative weighted quadratic sum. -/
theorem weighted_coordinate_moment {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (X : Ω → ι → ℝ) (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (M : ℝ)
    (hi : ∀ i, Integrable (fun ω ↦ X ω i ^ 2) μ)
    (hm : ∀ i, (∫ ω, X ω i ^ 2 ∂μ) ≤ M) :
    Integrable (fun ω ↦ ∑ i, e i * X ω i ^ 2) μ ∧
      (∫ ω, ∑ i, e i * X ω i ^ 2 ∂μ) ≤ M * ∑ i, e i := by
  have hh (i : ι) : Integrable (fun ω ↦ e i * X ω i ^ 2) μ := (hi i).const_mul _
  refine ⟨integrable_finset_sum _ (fun i _ ↦ hh i), ?_⟩
  rw [integral_finset_sum _ (fun i _ ↦ hh i)]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ i, e i * M := Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hm i) (he i))
    _ = M * ∑ i, e i := by rw [← Finset.sum_mul, mul_comm]

end SRWTightness
