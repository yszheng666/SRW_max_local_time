import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- Expected number of successes in a finite candidate set, with no independence requirement. -/
theorem finite_success_first_moment {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Finset ι) (E : ι → Set Ω)
    (hE : ∀ z ∈ Z, MeasurableSet (E z)) :
    (∫ ω, ∑ z ∈ Z, (E z).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) =
      ∑ z ∈ Z, μ.real (E z) := by
  rw [integral_finsetSum Z (fun z hz ↦ (integrable_const (1 : ℝ)).indicator (hE z hz))]
  apply Finset.sum_congr rfl
  intro z hz
  exact integral_indicator_one (hE z hz)

/-- Uniform one-point bounds give the corresponding finite success-count expectation bounds. -/
theorem finite_success_first_moment_bounds {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Finset ι) (E : ι → Set Ω)
    (hE : ∀ z ∈ Z, MeasurableSet (E z)) (a b : ℝ)
    (hb : ∀ z ∈ Z, a ≤ μ.real (E z) ∧ μ.real (E z) ≤ b) :
    (Z.card : ℝ) * a ≤ (∫ ω, ∑ z ∈ Z, (E z).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) ∧
      (∫ ω, ∑ z ∈ Z, (E z).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) ≤ (Z.card : ℝ) * b := by
  rw [finite_success_first_moment μ Z E hE]
  constructor
  · simpa using Finset.sum_le_sum (fun z hz ↦ (hb z hz).1)
  · simpa using Finset.sum_le_sum (fun z hz ↦ (hb z hz).2)

end SRWTightness
