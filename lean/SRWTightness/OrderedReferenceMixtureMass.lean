import SRWTightness.OrderedForestMixtureAuxiliary

open MeasureTheory
namespace SRWTightness

/-- The fixed-total reference measure has exactly the common finite count mass. -/
theorem ordered_reference_mixture_mass {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [Countable α] [Countable β]
    [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (hinput : OrderedForestMixtureInput α β) (μ₀ : Measure α) (μ₁ : Measure β)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) (label : Fin n → Bool) (k l : ℕ) :
    orderedTaggedCountMeasure p label μ₀ μ₁ k l Set.univ =
      ENNReal.ofReal (referenceJointCountWeight p label k l) := by
  have hh := congrArg (fun μ ↦ μ Set.univ)
    (hinput.concatenate μ₀ μ₁ inferInstance inferInstance p hp hp₁ n label k l)
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ] at hh
  simpa only [Set.preimage_univ, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using hh

/-- Reference mixture finiteness permits conversion of measure domination to real probabilities. -/
theorem ordered_reference_mixture_finite {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [Countable α] [Countable β]
    [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (hinput : OrderedForestMixtureInput α β) (μ₀ : Measure α) (μ₁ : Measure β)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) (label : Fin n → Bool) (k l : ℕ) :
    IsFiniteMeasure (orderedTaggedCountMeasure p label μ₀ μ₁ k l) := by
  constructor
  rw [ordered_reference_mixture_mass hinput μ₀ μ₁ p hp hp₁ n label k l]
  exact ENNReal.ofReal_lt_top

end SRWTightness
