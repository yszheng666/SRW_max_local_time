import SRWTightness.FiniteSuccessSecondMoment

open MeasureTheory
namespace SRWTightness

/-- A finite count of null measurable events is integrable. -/
theorem finite_success_integrable {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Finset ι) (E : ι → Set Ω)
    (hE : ∀ z ∈ Z, NullMeasurableSet (E z) μ) :
    Integrable (fun ω ↦ ∑ z ∈ Z, (E z).indicator (fun _ ↦ (1 : ℝ)) ω) μ := by
  exact integrable_finsetSum Z (fun z hz ↦ (integrable_const 1).indicator₀ (hE z hz))

/-- The square of a finite count of null measurable events is integrable. -/
theorem finite_success_square_integrable {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Finset ι) (E : ι → Set Ω)
    (hE : ∀ z ∈ Z, NullMeasurableSet (E z) μ) :
    Integrable (fun ω ↦ (∑ z ∈ Z, (E z).indicator (fun _ ↦ (1 : ℝ)) ω) ^ 2) μ := by
  simp_rw [finite_success_square Z E]
  exact integrable_finsetSum Z (fun z hz ↦ integrable_finsetSum Z
    (fun w hw ↦ (integrable_const 1).indicator₀ ((hE z hz).inter (hE w hw))))

end SRWTightness
