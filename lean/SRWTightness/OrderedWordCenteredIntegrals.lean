import SRWTightness.FirstEntranceWordMixtureFinite
import SRWTightness.ReferenceWordIntegral

open MeasureTheory
namespace SRWTightness

/-- Integrable killed-word components give an integrable actual first-entry mixture. -/
theorem integrable_firstEntranceWordMark (D K : Finset Site) (x : Site) (f : WordMark → ℝ)
    (hf : ∀ y ∈ K, Integrable f (killedWordMarkLaw D y)) :
    Integrable f (firstEntranceWordMarkLaw D K x) := by
  rw [firstEntranceWordMarkLaw_eq]
  apply Integrable.add_measure
  · exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  · exact integrable_finsetSum_measure.mpr (fun y hy ↦
      (hf y hy).smul_measure (measure_ne_top _ _))

/-- Real integration against the exact actual first-entry mixture. -/
theorem integral_firstEntranceWordMark (D K : Finset Site) (x : Site) (f : WordMark → ℝ)
    (hf : ∀ y ∈ K, Integrable f (killedWordMarkLaw D y)) :
    ∫ Y, f Y ∂firstEntranceWordMarkLaw D K x = competingExitMass D K x * f none +
      ∑ y ∈ K, (competingEntranceLaw D K x).real {y} * ∫ Y, f Y ∂killedWordMarkLaw D y := by
  rw [firstEntranceWordMarkLaw_eq]
  rw [integral_add_measure
    ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)
    (integrable_finsetSum_measure.mpr (fun y hy ↦
      (hf y hy).smul_measure (measure_ne_top _ _)))]
  rw [integral_finsetSum_measure (fun y hy ↦ (hf y hy).smul_measure (measure_ne_top _ _))]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (show 0 ≤ competingExitMass D K x from measureReal_nonneg)]
  rfl

/-- Centering at the empty word keeps the exact actual entrance weights. -/
theorem integral_firstEntranceWordMark_centered (D K : Finset Site) (x : Site)
    (f : WordMark → ℝ) (hf : ∀ y ∈ K, Integrable f (killedWordMarkLaw D y)) :
    ∫ Y, f Y ∂firstEntranceWordMarkLaw D K x = f none +
      ∑ y ∈ K, (competingEntranceLaw D K x).real {y} *
        ((∫ Y, f Y ∂killedWordMarkLaw D y) - f none) := by
  have hm := integral_firstEntranceWordMark D K x (fun _ ↦ (1 : ℝ))
    (fun _ _ ↦ integrable_const 1)
  have hmass : competingExitMass D K x +
      ∑ y ∈ K, (competingEntranceLaw D K x).real {y} = 1 := by
    simpa using hm.symm
  have hh := congrArg (fun r : ℝ ↦ r * f none) hmass
  rw [integral_firstEntranceWordMark D K x f hf]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  nlinarith only [hh]

/-- The reference ordered mixture has the matching centered equilibrium formula. -/
theorem integral_referenceWordMark_centered (D K : Finset Site) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (f : WordMark → ℝ)
    (hf : ∀ y ∈ K, Integrable f (killedWordMarkLaw D y)) :
    ∫ Y, f Y ∂referenceWordMarkLaw D K α = f none +
      ∑ y ∈ K, (α * equilibriumMeasure D K y) *
        ((∫ Y, f Y ∂killedWordMarkLaw D y) - f none) := by
  have hm : (∑ y ∈ K, α * equilibriumMeasure D K y) = α * capacity D K := by
    rw [← Finset.mul_sum]
    rfl
  rw [integral_referenceWordMark D K α hα hcap f hf]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hm]
  ring

end SRWTightness
