import SRWTightness.ReferenceSignedTilt

open MeasureTheory

namespace SRWTightness

/-- Every signed coefficient vector in the explicit l1 neighborhood has an integrable tilt.
The zero coefficient vector is included. -/
theorem referenceMark_linear_exponential_bound (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (4 * L)) :
    Integrable (fun Y : Mark K ↦ Real.exp (∑ z, β z * (Y z : ℝ)))
      (referenceMarkLaw D K α) ∧
    (∫ Y : Mark K, Real.exp (∑ z, β z * (Y z : ℝ)) ∂referenceMarkLaw D K α) ≤
      1 + 4 * α * (∑ z, |β z|) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  let B := ∑ z, |β z|
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun z _ ↦ abs_nonneg _)
  by_cases hBzero : B = 0
  · have hz (z : K) : β z = 0 := by
      apply abs_eq_zero.mp
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ ↦ abs_nonneg (β z))).mp hBzero z
        (Finset.mem_univ z)
    simp only [hz, abs_zero, zero_mul, Finset.sum_const_zero, Real.exp_zero, mul_zero, add_zero]
    exact ⟨integrable_const 1, by simp⟩
  · have hB : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBzero)
    let a : K → ℝ := fun z ↦ β z / B
    have ha : ∑ z, |a z| = 1 := by
      simp only [a, abs_div, abs_of_pos hB, ← Finset.sum_div]
      exact div_self hB.ne'
    have he := referenceMark_signed_exponential_bound D K hKD α hα hcap a ha L hL hG B
      (by simpa only [abs_of_pos hB] using hsmall)
    have hf : (fun Y : Mark K ↦ Real.exp (B * ∑ z, a z * (Y z : ℝ))) =
        (fun Y : Mark K ↦ Real.exp (∑ z, β z * (Y z : ℝ))) := by
      funext Y
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      dsimp [a]
      field_simp
    rw [hf, abs_of_pos hB] at he
    exact he

/-- The signed linear tilt of the actual mark law is normalized, including zero tilt. -/
theorem referenceMark_linear_tilt_probability (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (4 * L)) :
    IsProbabilityMeasure ((referenceMarkLaw D K α).tilted
      (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  exact isProbabilityMeasure_tilted
    (referenceMark_linear_exponential_bound D K hKD α hα hcap β L hL hG hsmall).1

end SRWTightness
