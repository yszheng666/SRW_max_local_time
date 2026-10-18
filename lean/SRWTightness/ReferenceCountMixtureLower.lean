import SRWTightness.LabeledRootCountMixture
import SRWTightness.FiniteConditionalLower

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- Pointwise positive-count comparisons sum to the original joint count event. -/
theorem reference_count_mixture_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ} (label : Fin n → Bool)
    (f : Ω → List ℕ) (X Y : Ω → ℕ) (p F : ℝ) (k l : ℕ)
    (hf : ∀ r : Fin n → ℕ, MeasurableSet {ω | f ω = List.ofFn r})
    (hcounts : ∀ᵐ ω ∂μ, ∀ r : Fin n → ℕ, f ω = List.ofFn r →
      X ω = labeledRootTotal label r false ∧ Y ω = labeledRootTotal label r true)
    (hpoint : ∀ r : Fin n → ℕ, (∀ i, 0 < r i) →
      labeledRootTotal label r false = k → labeledRootTotal label r true = l →
      (∏ i, p * (1-p) ^ (r i - 1)) ≤ Real.exp F * μ.real {ω | f ω = List.ofFn r}) :
    referenceJointCountWeight p label k l ≤ Real.exp F * μ.real {ω | X ω = k ∧ Y ω = l} := by
  classical
  apply finite_reference_count_lower μ f _ root_vector_list_injective
  · intro r _
    exact hf (fun i ↦ (r i).val)
  · filter_upwards [hcounts] with ω hω
    intro r hr he
    obtain ⟨_, hk, hl⟩ := (Finset.mem_filter.mp hr).2
    obtain ⟨hx, hy⟩ := hω _ he
    exact ⟨hx.trans hk, hy.trans hl⟩
  · intro r hr
    obtain ⟨hp, hk, hl⟩ := (Finset.mem_filter.mp hr).2
    exact hpoint _ hp hk hl

end SRWTightness
