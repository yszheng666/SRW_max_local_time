import SRWTightness.TaggedPositiveCountVector
import SRWTightness.TaggedFixedForestAtomSupport
import SRWTightness.TaggedForestAtomFactors

open MeasureTheory
open scoped BigOperators ENNReal

namespace SRWTightness

/-- The original positive-count box mixed with its exact independent tagged block kernels. -/
noncomputable def orderedTaggedFiniteCountMixture {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β) (p : ℝ) (n : ℕ)
    (label : Fin n → Bool) (k l : ℕ) :
    Measure (Fin n → Sum (List α) (List β)) :=
  ∑ j ∈ positiveRootVectors label k l,
    ENNReal.ofReal (taggedCountVectorWeight p (fun i ↦ (j i).val)) •
      Measure.pi (fun i ↦ taggedFixedForestLaw μ₀ μ₁ (label i) (j i).val)

/-- The complete original atomic count measure equals its finite exact-count kernel mixture. -/
theorem ordered_tagged_count_measure_decomposition {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) (label : Fin n → Bool) (k l : ℕ) :
    orderedTaggedCountMeasure p label μ₀ μ₁ k l =
      orderedTaggedFiniteCountMixture μ₀ μ₁ p n label k l := by
  classical
  apply Measure.ext_of_singleton
  intro r
  rw [orderedTaggedCountMeasure_singleton, orderedTaggedFiniteCountMixture,
    Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  by_cases hr : orderedTaggedCompatible label r ∧
      (orderedTaggedForests r).1.length = k ∧ (orderedTaggedForests r).2.length = l
  · let v := orderedTaggedRootVector n label r hr.1 k l hr.2.1 hr.2.2
    have hv : v ∈ positiveRootVectors label k l :=
      ordered_tagged_root_vector_mem n label r hr.1 k l hr.2.1 hr.2.2
    rw [Finset.sum_eq_single v]
    · have hc := (ordered_tagged_compatible_counts n label r).mp hr.1
      have hm : (Measure.pi (fun i ↦ taggedFixedForestLaw μ₀ μ₁ (label i) (v i).val)) {r} =
          ENNReal.ofReal (∏ i, taggedMarkAtomProduct μ₀ μ₁ (r i)) := by
        apply tagged_fixed_forest_pi_atom_match
        intro i
        exact ⟨(hc i).1, rfl⟩
      rw [hm, ordered_tagged_count_weight_factors μ₀ μ₁ p n label r hr.1 k l hr.2.1 hr.2.2,
        ENNReal.ofReal_mul (tagged_count_vector_weight_nonneg p _ hp hp₁)]
      rfl
    · intro j hj hjv
      have hz : (Measure.pi (fun i ↦ taggedFixedForestLaw μ₀ μ₁ (label i) (j i).val)) {r} =
          0 := by
        apply tagged_fixed_forest_pi_atom_zero_unless
        intro hcoord
        apply hjv
        exact ordered_tagged_root_vector_unique n label r hr.1 k l hr.2.1 hr.2.2 j
          (fun i ↦ (hcoord i).2.symm)
      rw [hz, mul_zero]
    · intro hnot
      exact (hnot hv).elim
  · rw [orderedTaggedCountWeight, if_neg hr, ENNReal.ofReal_zero]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hv : (∀ i, 0 < (j i).val) ∧
        labeledRootTotal label (fun i ↦ (j i).val) false = k ∧
        labeledRootTotal label (fun i ↦ (j i).val) true = l := by
      simpa only [positiveRootVectors, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have hz : (Measure.pi (fun i ↦ taggedFixedForestLaw μ₀ μ₁ (label i) (j i).val)) {r} =
        0 := by
      apply tagged_fixed_forest_pi_atom_zero_unless
      intro hcoord
      apply hr
      have hc : orderedTaggedCompatible label r := by
        apply (ordered_tagged_compatible_counts n label r).mpr
        intro i
        refine ⟨(hcoord i).1, ?_⟩
        rw [(hcoord i).2]
        exact hv.1 i
      have he : (fun i ↦ taggedBlockLength (r i)) = fun i ↦ (j i).val := by
        funext i
        exact (hcoord i).2
      have ht := ordered_tagged_forest_length_totals n label r hc
      refine ⟨hc, ?_, ?_⟩
      · rw [ht.1, he]
        exact hv.2.1
      · rw [ht.2, he]
        exact hv.2.2
    rw [hz, mul_zero]

end SRWTightness
