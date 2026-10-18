import SRWTightness.OrderedTaggedForestMixture

open MeasureTheory
namespace SRWTightness

/-- Standard ordered iid block concatenation with fixed two-label totals. This is a generic
reference-measure identity, with no source walk, geometry, error estimate, or success event. -/
structure OrderedForestMixtureInput (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α] [Countable β]
    [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)] : Prop where
  concatenate : ∀ (μ₀ : Measure α) (μ₁ : Measure β),
    IsProbabilityMeasure μ₀ → IsProbabilityMeasure μ₁ →
    ∀ (p : ℝ), 0 ≤ p → p ≤ 1 → ∀ (n : ℕ) (label : Fin n → Bool) (k l : ℕ),
      (orderedTaggedCountMeasure p label μ₀ μ₁ k l).map orderedTaggedForests =
        ENNReal.ofReal (referenceJointCountWeight p label k l) •
          ((independentForestLaw μ₀ k).prod (independentForestLaw μ₁ l))

end SRWTightness
