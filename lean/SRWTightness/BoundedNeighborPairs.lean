import SRWTightness.FiniteSuccessFirstMomentAE

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- Bounded-degree ordered pairs contribute at most the degree times the first moment. -/
theorem bounded_neighbor_pair_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Finset ι) (E : ι → Set Ω)
    (N : ι → Finset ι) (D : ℕ) (hD : ∀ z ∈ Z, (N z).card ≤ D) :
    (∑ z ∈ Z, ∑ w ∈ N z, μ.real (E z ∩ E w)) ≤
      (D : ℝ) * ∑ z ∈ Z, μ.real (E z) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  calc
    (∑ w ∈ N z, μ.real (E z ∩ E w)) ≤ ∑ _w ∈ N z, μ.real (E z) :=
      Finset.sum_le_sum (fun _ _ ↦ measureReal_mono Set.inter_subset_left)
    _ = ((N z).card : ℝ) * μ.real (E z) := by simp
    _ ≤ (D : ℝ) * μ.real (E z) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hD z hz) measureReal_nonneg

/-- The bounded-neighbor estimate applies to the actual indicator-sum expectation. -/
theorem bounded_neighbor_pair_first_moment {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Finset ι) (E : ι → Set Ω)
    (hE : ∀ z ∈ Z, NullMeasurableSet (E z) μ)
    (N : ι → Finset ι) (D : ℕ) (hD : ∀ z ∈ Z, (N z).card ≤ D) :
    (∑ z ∈ Z, ∑ w ∈ N z, μ.real (E z ∩ E w)) ≤
      (D : ℝ) * (∫ ω, ∑ z ∈ Z, (E z).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) := by
  rw [finite_success_first_moment_ae μ Z E hE]
  exact bounded_neighbor_pair_sum μ Z E N D hD

end SRWTightness
