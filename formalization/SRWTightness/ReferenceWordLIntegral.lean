import SRWTightness.ReferenceWordMark

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- Nonnegative integration of the full ordered reference mixture needs no finiteness premise. -/
theorem lintegral_referenceWordMark (D K : Finset Site) (α : ℝ) (f : WordMark → ℝ≥0∞) :
    (∫⁻ Y, f Y ∂referenceWordMarkLaw D K α) =
      ENNReal.ofReal (1 - α * capacity D K) * f none +
      ∑ x ∈ K, ENNReal.ofReal (α * equilibriumMeasure D K x) *
        ∫⁻ Y, f Y ∂killedWordMarkLaw D x := by
  rw [referenceWordMarkLaw, lintegral_add_measure, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul,
    lintegral_dirac' _ (measurable_of_countable _)]

end SRWTightness
