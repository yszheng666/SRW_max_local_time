import SRWTightness.FiniteSuccessFirstMomentAE

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- Squaring a finite successful-site count gives all ordered pair indicators, including the diagonal. -/
theorem finite_success_square {Ω ι : Type*} (Z : Finset ι) (E : ι → Set Ω) (ω : Ω) :
    (∑ z ∈ Z, (E z).indicator (fun _ ↦ (1 : ℝ)) ω) ^ 2 =
      ∑ z ∈ Z, ∑ w ∈ Z, (E z ∩ E w).indicator (fun _ ↦ (1 : ℝ)) ω := by
  classical
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hz' : ω ∈ E z <;> by_cases hw' : ω ∈ E w <;> simp [hz', hw']

/-- The true second moment is exactly the full ordered-pair success probability sum. -/
theorem finite_success_second_moment {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Finset ι) (E : ι → Set Ω)
    (hE : ∀ z ∈ Z, NullMeasurableSet (E z) μ) :
    (∫ ω, (∑ z ∈ Z, (E z).indicator (fun _ ↦ (1 : ℝ)) ω) ^ 2 ∂μ) =
      ∑ z ∈ Z, ∑ w ∈ Z, μ.real (E z ∩ E w) := by
  have hi (z : ι) (hz : z ∈ Z) (w : ι) (hw : w ∈ Z) :
      Integrable ((E z ∩ E w).indicator (fun _ ↦ (1 : ℝ))) μ := by
    apply ((integrable_const (1 : ℝ)).indicator
      (measurableSet_toMeasurable μ (E z ∩ E w))).congr
    exact indicator_ae_eq_of_ae_eq_set ((hE z hz).inter (hE w hw)).toMeasurable_ae_eq
  simp_rw [finite_success_square Z E]
  rw [integral_finsetSum Z (fun z hz ↦ integrable_finset_sum Z (hi z hz))]
  apply Finset.sum_congr rfl
  intro z hz
  rw [integral_finsetSum Z (hi z hz)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [integral_indicator₀ ((hE z hz).inter (hE w hw))]
  simp

end SRWTightness
