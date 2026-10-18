import SRWTightness.ReferenceSignedCgfTaylor

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual reference law has a cubic cgf remainder for every small physical coefficient
vector, including the zero vector. -/
theorem referenceMark_linear_cgf_taylor (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L)) :
    let V := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
    let μ := referenceMarkLaw D K α
    |cgf V μ 1 - (∫ Y, V Y ∂μ) -
      ((∫ Y, V Y ^ 2 ∂μ) - (∫ Y, V Y ∂μ) ^ 2) / 2| ≤
        23592976 * L ^ 3 * (∑ z, |β z|) ^ 3 / 6 := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  let B := ∑ z, |β z|
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  by_cases hB : B = 0
  · have hz (z : K) : β z = 0 := by
      apply abs_eq_zero.mp
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ ↦ abs_nonneg (β z))).mp hB
        z (Finset.mem_univ z)
    simp [hz, cgf_zero_fun]
  have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
  let a := fun z ↦ β z / B
  let U := fun Y : Mark K ↦ ∑ z, a z * (Y z : ℝ)
  let V := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  let μ := referenceMarkLaw D K α
  have ha : ∑ z, |a z| = 1 := by
    simp only [a, abs_div, abs_of_pos hBpos, ← Finset.sum_div]
    exact div_self hB
  have hV : V = fun Y ↦ B * U Y := by
    funext Y
    dsimp [V, U, a]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    field_simp
  have hcgf : cgf V μ 1 = cgf U μ B := by
    simp only [hV, cgf, mgf, one_mul]
  have hm : (∫ Y, V Y ∂μ) = B * ∫ Y, U Y ∂μ := by
    rw [hV, integral_const_mul]
  have h2 : (∫ Y, V Y ^ 2 ∂μ) = B ^ 2 * ∫ Y, U Y ^ 2 ∂μ := by
    simp only [hV, mul_pow, integral_const_mul]
  have ht := referenceMark_signed_cgf_taylor D K hKD α hα hcap a ha L hL hαL hG B
    (by simpa only [abs_of_pos hBpos] using hsmall)
  change |cgf V μ 1 - (∫ Y, V Y ∂μ) -
    ((∫ Y, V Y ^ 2 ∂μ) - (∫ Y, V Y ∂μ) ^ 2) / 2| ≤
      23592976 * L ^ 3 * B ^ 3 / 6
  calc
    _ = |cgf U μ B - (∫ Y, U Y ∂μ) * B -
      ((∫ Y, U Y ^ 2 ∂μ) - (∫ Y, U Y ∂μ) ^ 2) * B ^ 2 / 2| := by
        rw [hcgf, hm, h2]
        congr 1
        ring
    _ ≤ _ := by simpa only [abs_of_pos hBpos] using ht

end SRWTightness
