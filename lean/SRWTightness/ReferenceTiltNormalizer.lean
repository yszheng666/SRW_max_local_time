import SRWTightness.ReferenceLinearTilt

open MeasureTheory

namespace SRWTightness

/-- Small signed tilts have a denominator bounded away from zero under the actual mark law. -/
theorem referenceMark_tilt_normalizer_lower (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L)) :
    7 / 8 ≤ (∫ Y : Mark K, Real.exp (∑ z, β z * (Y z : ℝ)) ∂referenceMarkLaw D K α) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hB0 : 0 ≤ ∑ z, |β z| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have hB8 := (le_div_iff₀ (by positivity : 0 < 8 * L)).mp hsmall
  have hB4 : (∑ z, |β z|) ≤ 1 / (4 * L) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have he := (referenceMark_linear_exponential_bound D K hKD α hα hcap β L hL hG hB4).1
  have hi (z : K) : Integrable (fun Y : Mark K ↦ (Y z : ℝ)) (referenceMarkLaw D K α) :=
    integrable_referenceMark D K α _ (fun x _ ↦ integrable_killedMark_coordinate D K x z)
  have hif : Integrable (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)) (referenceMarkLaw D K α) :=
    integrable_finsetSum _ (fun z _ ↦ (hi z).const_mul (β z))
  have hiLower : Integrable (fun Y : Mark K ↦ 1 + ∑ z, β z * (Y z : ℝ))
      (referenceMarkLaw D K α) := (integrable_const 1).add hif
  have hh := integral_mono hiLower he
    (fun Y : Mark K ↦ by linarith [Real.add_one_le_exp (∑ z, β z * (Y z : ℝ))])
  rw [integral_add (integrable_const 1) hif, integral_const,
    integral_finsetSum _ (fun z _ ↦ (hi z).const_mul (β z))] at hh
  simp only [probReal_univ, smul_eq_mul, one_mul] at hh
  simp_rw [integral_const_mul, referenceMark_mean D K hKD α hα hcap] at hh
  rw [← Finset.sum_mul] at hh
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset K)) ↦ neg_abs_le (β z))
  rw [Finset.sum_neg_distrib] at hsum
  have hl := mul_le_mul_of_nonneg_right hsum hα
  have hαB := mul_le_mul_of_nonneg_right hαL hB0
  nlinarith

/-- The doubled signed tilt is integrable and its exponential moment is uniformly bounded. -/
theorem referenceMark_double_tilt_bound (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L)) :
    Integrable (fun Y : Mark K ↦ Real.exp (2 * ∑ z, β z * (Y z : ℝ))) (referenceMarkLaw D K α) ∧
    (∫ Y : Mark K, Real.exp (2 * ∑ z, β z * (Y z : ℝ)) ∂referenceMarkLaw D K α) ≤ 2 := by
  have hB0 : 0 ≤ ∑ z, |β z| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have hB8 := (le_div_iff₀ (by positivity : 0 < 8 * L)).mp hsmall
  have hsum : (∑ z, |2 * β z|) = 2 * ∑ z, |β z| := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), Finset.mul_sum]
  have hc : (∑ z, |2 * β z|) ≤ 1 / (4 * L) := by
    rw [hsum]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hh := referenceMark_linear_exponential_bound D K hKD α hα hcap
    (fun z ↦ 2 * β z) L hL hG hc
  have hf : (fun Y : Mark K ↦ Real.exp (∑ z, (2 * β z) * (Y z : ℝ))) =
      (fun Y : Mark K ↦ Real.exp (2 * ∑ z, β z * (Y z : ℝ))) := by
    funext Y
    simp only [Finset.mul_sum, mul_assoc]
  rw [hf, hsum] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hαB := mul_le_mul_of_nonneg_right hαL hB0
  nlinarith

end SRWTightness
