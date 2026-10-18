import SRWTightness.TaggedFixedForestLaw
import SRWTightness.TaggedForestPrepend
import SRWTightness.FiniteProductConsLaw
import SRWTightness.IndependentForestPrependPair
import SRWTightness.IndependentForestEmpty

open MeasureTheory

namespace SRWTightness

/-- Fixed tagged block counts concatenate to the two original independent ordered forest laws. -/
theorem tagged_fixed_forest_concatenation {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (n : ℕ) (label : Fin n → Bool) (r : Fin n → ℕ) :
    (Measure.pi (fun i ↦ taggedFixedForestLaw μ₀ μ₁ (label i) (r i))).map
      orderedTaggedForests =
      (independentForestLaw μ₀ (labeledRootTotal label r false)).prod
        (independentForestLaw μ₁ (labeledRootTotal label r true)) := by
  induction n with
  | zero =>
    have hf : (@orderedTaggedForests α β 0) = fun _ ↦ ([], []) := by
      funext ξ
      simp [orderedTaggedForests, taggedForestLeft, taggedForestRight]
    rw [hf, Measure.map_const, measure_univ, one_smul]
    simp [labeledRootTotal, independent_forest_empty_law, Measure.dirac_prod_dirac]
  | succ n ih =>
    let lt : Fin n → Bool := fun i ↦ label i.succ
    let rt : Fin n → ℕ := fun i ↦ r i.succ
    let ν := Measure.pi (fun i ↦ taggedFixedForestLaw μ₀ μ₁ (lt i) (rt i))
    rw [← finite_product_cons_law n (fun i ↦ taggedFixedForestLaw μ₀ μ₁ (label i) (r i)),
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    have hf : (@orderedTaggedForests α β (n + 1) ∘
        (fun q : Sum (List α) (List β) × (Fin n → Sum (List α) (List β)) ↦
          Fin.cons q.1 q.2)) =
        (fun q ↦ taggedForestPrepend q.1 q.2) ∘
          Prod.map id (@orderedTaggedForests α β n) := by
      funext q
      exact ordered_tagged_forests_cons n q.1 q.2
    rw [hf, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    change (((taggedFixedForestLaw μ₀ μ₁ (label 0) (r 0)).prod ν).map
      (Prod.map id (@orderedTaggedForests α β n))).map
        (fun q ↦ taggedForestPrepend q.1 q.2) = _
    rw [← Measure.map_prod_map (taggedFixedForestLaw μ₀ μ₁ (label 0) (r 0)) ν
      measurable_id (measurable_of_countable _), Measure.map_id]
    have hh := ih lt rt
    change ν.map orderedTaggedForests = _ at hh
    rw [hh]
    rw [labeled_root_total_cons n label r false, labeled_root_total_cons n label r true]
    cases hc : label 0 with
    | false =>
      simp only [hc, Bool.false_eq_true, if_true, if_false, zero_add]
      rw [taggedFixedForestLaw]
      have hm : ((independentForestLaw μ₀ (r 0)).map
          (Sum.inl : List α → Sum (List α) (List β))).prod
          ((independentForestLaw μ₀ (labeledRootTotal lt rt false)).prod
            (independentForestLaw μ₁ (labeledRootTotal lt rt true))) =
          ((independentForestLaw μ₀ (r 0)).prod
            ((independentForestLaw μ₀ (labeledRootTotal lt rt false)).prod
              (independentForestLaw μ₁ (labeledRootTotal lt rt true)))).map
                (Prod.map (Sum.inl : List α → Sum (List α) (List β)) id) := by
        simpa only [Measure.map_id] using Measure.map_prod_map
          (f := (Sum.inl : List α → Sum (List α) (List β)))
          (independentForestLaw μ₀ (r 0))
          ((independentForestLaw μ₀ (labeledRootTotal lt rt false)).prod
            (independentForestLaw μ₁ (labeledRootTotal lt rt true))) measurable_inl measurable_id
      rw [hm, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      exact independent_forest_prepend_left μ₀ μ₁ (r 0)
        (labeledRootTotal lt rt false) (labeledRootTotal lt rt true)
    | true =>
      simp only [hc, Bool.true_eq_false, if_true, if_false, zero_add]
      rw [taggedFixedForestLaw]
      have hm : ((independentForestLaw μ₁ (r 0)).map
          (Sum.inr : List β → Sum (List α) (List β))).prod
          ((independentForestLaw μ₀ (labeledRootTotal lt rt false)).prod
            (independentForestLaw μ₁ (labeledRootTotal lt rt true))) =
          ((independentForestLaw μ₁ (r 0)).prod
            ((independentForestLaw μ₀ (labeledRootTotal lt rt false)).prod
              (independentForestLaw μ₁ (labeledRootTotal lt rt true)))).map
                (Prod.map (Sum.inr : List β → Sum (List α) (List β)) id) := by
        simpa only [Measure.map_id] using Measure.map_prod_map
          (f := (Sum.inr : List β → Sum (List α) (List β)))
          (independentForestLaw μ₁ (r 0))
          ((independentForestLaw μ₀ (labeledRootTotal lt rt false)).prod
            (independentForestLaw μ₁ (labeledRootTotal lt rt true))) measurable_inr measurable_id
      rw [hm, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      exact independent_forest_prepend_right μ₀ μ₁ (r 0)
        (labeledRootTotal lt rt false) (labeledRootTotal lt rt true)

end SRWTightness
