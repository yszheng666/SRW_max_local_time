import SRWTightness.ReferenceWordMark

open MeasureTheory
namespace SRWTightness

/-- Integrability under the ordered reference mixture follows from its killed-word components. -/
theorem integrable_referenceWordMark (D K : Finset Site) (α : ℝ) (f : WordMark → ℝ)
    (hf : ∀ x ∈ K, Integrable f (killedWordMarkLaw D x)) :
    Integrable f (referenceWordMarkLaw D K α) := by
  apply Integrable.add_measure
  · exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  · exact integrable_finsetSum_measure.mpr (fun x hx ↦
      (hf x hx).smul_measure ENNReal.ofReal_ne_top)

/-- Exact integration against the ordered reference mixture, including its empty mark. -/
theorem integral_referenceWordMark (D K : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (f : WordMark → ℝ)
    (hf : ∀ x ∈ K, Integrable f (killedWordMarkLaw D x)) :
    ∫ Y, f Y ∂referenceWordMarkLaw D K α = (1 - α * capacity D K) * f none +
      ∑ x ∈ K, (α * equilibriumMeasure D K x) * ∫ Y, f Y ∂killedWordMarkLaw D x := by
  unfold referenceWordMarkLaw
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

end SRWTightness
