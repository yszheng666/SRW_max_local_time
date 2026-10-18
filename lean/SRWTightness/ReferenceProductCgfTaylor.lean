import SRWTightness.ReferenceLinearCgfTaylor
import SRWTightness.ProductCgf
import SRWTightness.IndependentMarks
import SRWTightness.ReferenceLinearMoment

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Exact first moment of every signed linear reference-mark observation. -/
theorem referenceMark_linear_mean (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (β : K → ℝ) :
    (∫ Y : Mark K, (∑ z, β z * (Y z : ℝ)) ∂referenceMarkLaw D K α) = α * ∑ z, β z := by
  rw [integral_finsetSum Finset.univ (fun z _ ↦
    (integrable_referenceMark D K α _
      (fun x _ ↦ integrable_killedMark_coordinate D K x z)).const_mul (β z))]
  simp_rw [integral_const_mul, referenceMark_mean D K hKD α hα hcap]
  rw [← Finset.sum_mul]
  ring

/-- The centered sum of actual independent marks has at most the sum of the cubic cgf errors. -/
theorem referenceMark_product_cgf_taylor (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L)) (k : ℕ) :
    let V := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
    let μ := referenceMarkLaw D K α
    |cgf (fun Y : MarkSamples K k ↦ (∑ i, V (Y i)) - k * ∫ Z, V Z ∂μ)
      (markProductLaw D K α k) 1 -
        k * ((∫ Y, V Y ^ 2 ∂μ) - (∫ Y, V Y ∂μ) ^ 2) / 2| ≤
          k * 23592976 * L ^ 3 * (∑ z, |β z|) ^ 3 / 6 := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hB4 := hsmall.trans
    (one_div_le_one_div_of_le (by positivity : 0 < 4 * L) (by linarith : 4 * L ≤ 8 * L))
  have hi := (referenceMark_linear_exponential_bound D K hKD α hα hcap β L hL hG hB4).1
  have ht := referenceMark_linear_cgf_taylor D K hKD α hα hcap β L hL hαL hG hsmall
  dsimp only
  unfold markProductLaw
  rw [cgf_iid_centered_sum _ _ _ _ hi]
  have he (a b c : ℝ) : (k : ℝ) * (a - b) - k * c / 2 = k * (a - b - c / 2) := by ring
  rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
  calc
    _ ≤ (k : ℝ) * (23592976 * L ^ 3 * (∑ z, |β z|) ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg k)
    _ = _ := by ring

/-- The actual centered product cgf is approximated by its explicit Green-energy polynomial. -/
theorem referenceMark_product_cgf_green_taylor (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L)) (k : ℕ) :
    |cgf (fun Y : MarkSamples K k ↦
      (∑ i, ∑ z, β z * (Y i z : ℝ)) - k * (α * ∑ z, β z))
      (markProductLaw D K α k) 1 -
        k * (2 * α * (∑ y : K, ∑ z : K, β y * killedGreen D y z * β z) -
          α * (∑ z, β z ^ 2) - (α * ∑ z, β z) ^ 2) / 2| ≤
            k * 23592976 * L ^ 3 * (∑ z, |β z|) ^ 3 / 6 := by
  have ht := referenceMark_product_cgf_taylor D K hKD α hα hcap β L hL hαL hG hsmall k
  dsimp only at ht
  rwa [referenceMark_linear_mean D K hKD α hα hcap β,
    referenceMark_linear_second_moment D K hKD α hα hcap β] at ht

end SRWTightness
