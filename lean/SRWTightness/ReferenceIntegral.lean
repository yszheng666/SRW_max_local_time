import SRWTightness.ReferenceMark

open MeasureTheory

namespace SRWTightness

 theorem integrable_referenceMark (D K : Finset Site) (α : ℝ) (f : Mark K → ℝ)
    (hf : ∀ x ∈ K, Integrable f (killedMarkLaw D K x)) :
    Integrable f (referenceMarkLaw D K α) := by
  apply Integrable.add_measure
  · exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  · exact integrable_finsetSum_measure.mpr (fun x hx ↦
      (hf x hx).smul_measure ENNReal.ofReal_ne_top)

 theorem integral_referenceMark (D K : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (f : Mark K → ℝ)
    (hf : ∀ x ∈ K, Integrable f (killedMarkLaw D K x)) :
    ∫ Y, f Y ∂referenceMarkLaw D K α = (1 - α * capacity D K) * f 0 +
      ∑ x ∈ K, (α * equilibriumMeasure D K x) * ∫ Y, f Y ∂killedMarkLaw D K x := by
  unfold referenceMarkLaw
  rw [integral_add_measure
    ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)
    (integrable_finsetSum_measure.mpr (fun x hx ↦
      (hf x hx).smul_measure ENNReal.ofReal_ne_top))]
  rw [integral_finsetSum_measure (fun x hx ↦ (hf x hx).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hcap)]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [ENNReal.toReal_ofReal (mul_nonneg hα (equilibriumMeasure_nonneg D K x))]

/-- Exact coordinate mean of the reference mark, without an asymptotic approximation. -/
theorem referenceMark_mean (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (z : K) :
    ∫ Y, (Y z : ℝ) ∂referenceMarkLaw D K α = α := by
  rw [integral_referenceMark D K α hα hcap _
    (fun x _ ↦ integrable_killedMark_coordinate D K x z)]
  simp only [Pi.zero_apply, Nat.cast_zero, mul_zero, zero_add, integral_killedMark_coordinate]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, equilibrium_green_on_set D K hKD z z.property, mul_one]

end SRWTightness
