import SRWTightness.ReferenceWordIntegral
import SRWTightness.KilledWordRootMean

open MeasureTheory
namespace SRWTightness

/-- The root count is integrable under the ordered reference law. -/
theorem integrable_referenceWordMark_roots (hLast : FiniteLastVisitCountInput)
    (D K L C : Finset Site) (hLC : L ⊆ C) (hCD : C ⊆ D) (α : ℝ) :
    Integrable (fun Y ↦ (wordMarkRootCount L C Y : ℝ)) (referenceWordMarkLaw D K α) :=
  integrable_referenceWordMark D K α _
    (fun x _ ↦ integrable_killedWordMark_roots hLast D L C hLC hCD x)

/-- The last-visit identity and equilibrium Green identity give the exact reference root mean.
Reference mixing and finite sums are internal; only generic finite-walk counting is an input. -/
theorem referenceWordMark_root_mean (hLast : FiniteLastVisitCountInput)
    (D K L C : Finset Site) (hKD : K ⊆ D) (hLK : L ⊆ K) (hLC : L ⊆ C)
    (hCD : C ⊆ D) (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) :
    (∫ Y, (wordMarkRootCount L C Y : ℝ) ∂referenceWordMarkLaw D K α) =
      α * capacity C L := by
  rw [integral_referenceWordMark D K α hα hcap _
    (fun x _ ↦ integrable_killedWordMark_roots hLast D L C hLC hCD x)]
  simp only [show wordMarkRootCount L C none = 0 from rfl,
    Nat.cast_zero, mul_zero, zero_add]
  simp_rw [integral_killedWordMark_roots hLast D L C hLC hCD, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y ∈ L, (∑ x ∈ K, equilibriumMeasure D K x * killedGreen D x y) *
        (α * equilibriumMeasure C L y) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ y ∈ L, α * equilibriumMeasure C L y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [equilibrium_green_on_set D K hKD y (hLK hy), one_mul]
    _ = α * capacity C L := by rw [← Finset.mul_sum]; rfl

end SRWTightness
