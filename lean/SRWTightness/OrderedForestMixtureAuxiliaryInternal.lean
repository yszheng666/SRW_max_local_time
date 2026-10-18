import SRWTightness.OrderedForestMixtureAuxiliary
import SRWTightness.OrderedForestMixtureInternal

open MeasureTheory
namespace SRWTightness

/-- Ordered concatenation remains valid after adjoining and pairing independent auxiliaries. -/
theorem ordered_mixture_auxiliary_law_internal {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [Countable α] [Countable β]
    [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ₀ : Measure α) (μ₁ : Measure β)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (σ : Measure γ) (τ : Measure δ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) (label : Fin n → Bool) (k l : ℕ) :
    ((orderedTaggedCountMeasure p label μ₀ μ₁ k l).prod (σ.prod τ)).map
      (fun q ↦ (((orderedTaggedForests q.1).1, q.2.1),
        ((orderedTaggedForests q.1).2, q.2.2))) =
      ENNReal.ofReal (referenceJointCountWeight p label k l) •
        (((independentForestLaw μ₀ k).prod σ).prod ((independentForestLaw μ₁ l).prod τ)) := by
  have hinput : OrderedForestMixtureInput α β := ordered_forest_mixture_input_internal α β
  let ρ := orderedTaggedCountMeasure p label μ₀ μ₁ k l
  have hf : Measurable (@orderedTaggedForests α β n) := measurable_of_countable _
  have hb : (ρ.prod (σ.prod τ)).map (Prod.map orderedTaggedForests id) =
      ENNReal.ofReal (referenceJointCountWeight p label k l) •
        (((independentForestLaw μ₀ k).prod (independentForestLaw μ₁ l)).prod (σ.prod τ)) := by
    rw [← Measure.map_prod_map ρ (σ.prod τ) hf measurable_id, Measure.map_id]
    rw [hinput.concatenate μ₀ μ₁ inferInstance inferInstance p hp hp₁ n label k l,
      Measure.prod_smul_left]
  have hr := product_pair_reorder (independentForestLaw μ₀ k) (independentForestLaw μ₁ l) σ τ
  have he := congrArg (Measure.map (fun q : (List α × List β) × (γ × δ) ↦
    ((q.1.1, q.2.1), (q.1.2, q.2.2)))) hb
  rw [Measure.map_map hr.measurable (hf.prodMap measurable_id), Measure.map_smul, hr.map_eq] at he
  exact he

/-- The reference mixture success mass is the same count weight times the two full forest success
probabilities, including their independent auxiliary variables. -/
theorem ordered_mixture_success_probability_internal {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [Countable α] [Countable β]
    [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ₀ : Measure α) (μ₁ : Measure β)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (σ : Measure γ) (τ : Measure δ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) (label : Fin n → Bool) (k l : ℕ)
    (E₀ : Set (List α × γ)) (E₁ : Set (List β × δ))
    (hE₀ : MeasurableSet E₀) (hE₁ : MeasurableSet E₁) :
    ((orderedTaggedCountMeasure p label μ₀ μ₁ k l).prod (σ.prod τ)).real
      {q | ((orderedTaggedForests q.1).1, q.2.1) ∈ E₀ ∧
        ((orderedTaggedForests q.1).2, q.2.2) ∈ E₁} =
      referenceJointCountWeight p label k l *
        (((independentForestLaw μ₀ k).prod σ).real E₀ *
          ((independentForestLaw μ₁ l).prod τ).real E₁) := by
  have hh := ordered_mixture_auxiliary_law_internal μ₀ μ₁ σ τ p hp hp₁ n label k l
  have hm := congrArg (fun μ ↦ μ.real (E₀ ×ˢ E₁)) hh
  have hf : Measurable (fun q : (Fin n → Sum (List α) (List β)) × (γ × δ) ↦
      (((orderedTaggedForests q.1).1, q.2.1), ((orderedTaggedForests q.1).2, q.2.2))) := by
    have h : Measurable (fun q : (Fin n → Sum (List α) (List β)) × (γ × δ) ↦
        orderedTaggedForests q.1) :=
      (measurable_of_countable (@orderedTaggedForests α β n)).comp measurable_fst
    exact (h.fst.prodMk measurable_snd.fst).prodMk (h.snd.prodMk measurable_snd.snd)
  rw [map_measureReal_apply hf (hE₀.prod hE₁)] at hm
  calc
    _ = _ := hm
    _ = referenceJointCountWeight p label k l *
        ((((independentForestLaw μ₀ k).prod σ).prod
          ((independentForestLaw μ₁ l).prod τ)).real (E₀ ×ˢ E₁)) := by
      unfold Measure.real
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (referenceJointCountWeight_nonneg p label k l hp hp₁)]
    _ = _ := by rw [measureReal_prod_prod]

end SRWTightness
