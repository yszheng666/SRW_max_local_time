import SRWTightness.FiniteSuccessFirstMoment

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- Continuous success events may be only null measurable; their finite count still has the usual mean. -/
theorem finite_success_first_moment_ae {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Finset ι) (E : ι → Set Ω)
    (hE : ∀ z ∈ Z, NullMeasurableSet (E z) μ) :
    (∫ ω, ∑ z ∈ Z, (E z).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) =
      ∑ z ∈ Z, μ.real (E z) := by
  have hi (z : ι) (hz : z ∈ Z) :
      Integrable ((E z).indicator (fun _ ↦ (1 : ℝ))) μ := by
    apply ((integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable μ (E z))).congr
    exact indicator_ae_eq_of_ae_eq_set (hE z hz).toMeasurable_ae_eq
  rw [integral_finsetSum Z hi]
  apply Finset.sum_congr rfl
  intro z hz
  rw [integral_indicator₀ (hE z hz)]
  simp

/-- Null measurable one-point probability bounds imply bounds for the actual expected count. -/
theorem finite_success_first_moment_ae_bounds {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Finset ι) (E : ι → Set Ω)
    (hE : ∀ z ∈ Z, NullMeasurableSet (E z) μ) (a b : ℝ)
    (hb : ∀ z ∈ Z, a ≤ μ.real (E z) ∧ μ.real (E z) ≤ b) :
    (Z.card : ℝ) * a ≤ (∫ ω, ∑ z ∈ Z, (E z).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) ∧
      (∫ ω, ∑ z ∈ Z, (E z).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) ≤ (Z.card : ℝ) * b := by
  rw [finite_success_first_moment_ae μ Z E hE]
  constructor
  · simpa using Finset.sum_le_sum (fun z hz ↦ (hb z hz).1)
  · simpa using Finset.sum_le_sum (fun z hz ↦ (hb z hz).2)

end SRWTightness
