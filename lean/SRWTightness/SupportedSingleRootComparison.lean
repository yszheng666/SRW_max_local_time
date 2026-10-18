import SRWTightness.SingleRootRecordComparison
import SRWTightness.SupportedRecordComparison

open MeasureTheory

namespace SRWTightness

/-- Exactly-one-root comparison with entrance and exit estimates only on their actual supports. -/
theorem supported_single_root_record_comparison {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (I : Measure X) [IsFiniteMeasure I] (S : X → Measure X)
    (hSf : ∀ x, IsFiniteMeasure (S x)) (A B : Set X)
    (hIs : ∀ᵐ x ∂I, x ∈ A) (hSs : ∀ x ∈ A, ∀ᵐ y ∂S x, y ∈ B)
    (q : X → ℝ) (c₁ c₂ η Q : ℝ) (hc₂ : 0 ≤ c₂) (hQ : 0 ≤ Q)
    (hI : c₁ ≤ I.real Set.univ ∧ I.real Set.univ ≤ 1)
    (hq : ∀ y ∈ B, c₂ ≤ q y ∧ q y ≤ 1)
    (hS : ∀ x ∈ A, Real.exp (-η) * Q ≤ (S x).real Set.univ ∧
      (S x).real Set.univ ≤ Real.exp η * Q) :
    c₁ * c₂ * Real.exp (-η) * Q ≤ singleRootRecordWeight I S q ∧
      singleRootRecordWeight I S q ≤ Real.exp η * Q := by
  let f := fun x ↦ ∫ y, q y ∂S x
  have hf : ∀ x ∈ A, c₂ * (Real.exp (-η) * Q) ≤ f x ∧ f x ≤ Real.exp η * Q := by
    intro x hx
    letI := hSf x
    have hh := integral_bounds_on_support (S x) B (hSs x hx) q c₂ 1 hc₂ hq
    refine ⟨(mul_le_mul_of_nonneg_left (hS x hx).1 hc₂).trans hh.1, ?_⟩
    simpa only [one_mul] using hh.2.trans (by simpa only [one_mul] using (hS x hx).2)
  have hh := integral_bounds_on_support I A hIs f (c₂ * (Real.exp (-η) * Q))
    (Real.exp η * Q) (by positivity) hf
  constructor
  · calc
      _ = (c₂ * (Real.exp (-η) * Q)) * c₁ := by ring
      _ ≤ (c₂ * (Real.exp (-η) * Q)) * I.real Set.univ :=
        mul_le_mul_of_nonneg_left hI.1 (by positivity)
      _ ≤ _ := hh.1
  · calc
      _ ≤ (Real.exp η * Q) * I.real Set.univ := hh.2
      _ ≤ (Real.exp η * Q) * 1 := mul_le_mul_of_nonneg_left hI.2 (by positivity)
      _ = _ := mul_one _

end SRWTightness
