import SRWTightness.Capacity

namespace SRWTightness

/-- A Green estimate only on equilibrium support controls reciprocal capacity. -/
theorem capacity_inverse_flatness (D K : Finset Site) (hKD : K ⊆ D)
    (z : Site) (hz : z ∈ K) (c ε : ℝ)
    (hflat : ∀ x ∈ K, equilibriumMeasure D K x ≠ 0 →
      |killedGreen D x z - c| ≤ ε) :
    |1 / capacity D K - c| ≤ ε := by
  have hne : K.Nonempty := ⟨z, hz⟩
  have hl : ∑ x ∈ K, equilibriumWeight D K x * (c - ε) ≤
      ∑ x ∈ K, equilibriumWeight D K x * killedGreen D x z := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases he : equilibriumMeasure D K x = 0
    · simp [equilibriumWeight, he]
    · have h := (abs_le.mp (hflat x hx he)).1
      exact mul_le_mul_of_nonneg_left (by linarith) (equilibriumWeight_nonneg D K x)
  have hu : ∑ x ∈ K, equilibriumWeight D K x * killedGreen D x z ≤
      ∑ x ∈ K, equilibriumWeight D K x * (c + ε) := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases he : equilibriumMeasure D K x = 0
    · simp [equilibriumWeight, he]
    · have h := (abs_le.mp (hflat x hx he)).2
      exact mul_le_mul_of_nonneg_left (by linarith) (equilibriumWeight_nonneg D K x)
  rw [← Finset.sum_mul, equilibriumWeight_sum D K hKD hne, one_mul,
    equilibriumWeight_green D K hKD z hz] at hl
  rw [← Finset.sum_mul, equilibriumWeight_sum D K hKD hne, one_mul,
    equilibriumWeight_green D K hKD z hz] at hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The error representation in the reciprocal capacity formula is exact. -/
theorem capacity_eq_inverse_with_error (D K : Finset Site) (hKD : K ⊆ D)
    (z : Site) (hz : z ∈ K) (c ε : ℝ)
    (hflat : ∀ x ∈ K, equilibriumMeasure D K x ≠ 0 →
      |killedGreen D x z - c| ≤ ε) :
    ∃ δ : ℝ, |δ| ≤ ε ∧ capacity D K = (c + δ)⁻¹ := by
  refine ⟨1 / capacity D K - c, capacity_inverse_flatness D K hKD z hz c ε hflat, ?_⟩
  simp

end SRWTightness
