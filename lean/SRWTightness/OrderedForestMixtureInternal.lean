import SRWTightness.TaggedCountMixtureDecomposition
import SRWTightness.TaggedFixedForestConcatenation
import SRWTightness.ExternalOrderedForestMixture
import Mathlib.Data.ENNReal.BigOperators

open MeasureTheory
open scoped BigOperators ENNReal

namespace SRWTightness

/-- The original fixed-total tagged count measure has its exact two-forest concatenation law. -/
theorem ordered_tagged_count_concatenation_internal {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) (label : Fin n → Bool) (k l : ℕ) :
    (orderedTaggedCountMeasure p label μ₀ μ₁ k l).map orderedTaggedForests =
      ENNReal.ofReal (referenceJointCountWeight p label k l) •
        ((independentForestLaw μ₀ k).prod (independentForestLaw μ₁ l)) := by
  classical
  rw [ordered_tagged_count_measure_decomposition μ₀ μ₁ p hp hp₁,
    orderedTaggedFiniteCountMixture,
    Measure.map_finset_sum (measurable_of_countable _).aemeasurable]
  simp only [Measure.map_smul]
  calc
    _ = ∑ j ∈ positiveRootVectors label k l,
        ENNReal.ofReal (taggedCountVectorWeight p (fun i ↦ (j i).val)) •
          ((independentForestLaw μ₀ k).prod (independentForestLaw μ₁ l)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hv : (∀ i, 0 < (j i).val) ∧
          labeledRootTotal label (fun i ↦ (j i).val) false = k ∧
          labeledRootTotal label (fun i ↦ (j i).val) true = l := by
        simpa only [positiveRootVectors, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      rw [tagged_fixed_forest_concatenation, hv.2.1, hv.2.2]
    _ = ENNReal.ofReal (∑ j ∈ positiveRootVectors label k l,
        taggedCountVectorWeight p (fun i ↦ (j i).val)) •
          ((independentForestLaw μ₀ k).prod (independentForestLaw μ₁ l)) := by
      rw [← Finset.sum_smul, ENNReal.ofReal_sum_of_nonneg
        (fun j _ ↦ tagged_count_vector_weight_nonneg p (fun i ↦ (j i).val) hp hp₁)]
    _ = _ := rfl

/-- The entire original ordered fixed-count forest mixture input is internally inhabited. -/
theorem ordered_forest_mixture_input_internal (α β : Type*) [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)] :
    OrderedForestMixtureInput α β := by
  constructor
  intro μ₀ μ₁ hμ₀ hμ₁ p hp hp₁ n label k l
  letI := hμ₀
  letI := hμ₁
  exact ordered_tagged_count_concatenation_internal μ₀ μ₁ p hp hp₁ n label k l

end SRWTightness
