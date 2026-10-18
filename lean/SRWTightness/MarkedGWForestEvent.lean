import SRWTightness.ExternalMarkedGWForestJoint

open MeasureTheory
namespace SRWTightness

/-- Forest population and terminal-mark events remain measurable with arbitrary independent auxiliaries. -/
theorem markedGWForestEvent_measurable {M Ξ : Type*} [Countable M] [MeasurableSpace Ξ]
    (n : ℕ) [MeasurableSpace (List (FiniteExcursionRecord M n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord M n))]
    [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)]
    (s : Set GeometricGWRecord) (E : GeometricGWRecord → Set (List M × Ξ))
    (hE : ∀ g, MeasurableSet (E g)) :
    MeasurableSet {p : List (FiniteExcursionRecord M n) × Ξ |
      forestPopulationList n p.1 ∈ s ∧
      (p.1.flatMap (finiteRecordLeaves n), p.2) ∈ E (forestPopulationList n p.1)} := by
  letI := finiteExcursionRecord_countable M n
  have he : {p : List (FiniteExcursionRecord M n) × Ξ |
      forestPopulationList n p.1 ∈ s ∧
      (p.1.flatMap (finiteRecordLeaves n), p.2) ∈ E (forestPopulationList n p.1)} =
      ⋃ rs : List (FiniteExcursionRecord M n),
        {p | p.1 = rs ∧ forestPopulationList n rs ∈ s ∧
          (rs.flatMap (finiteRecordLeaves n), p.2) ∈ E (forestPopulationList n rs)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    simp
  rw [he]
  apply MeasurableSet.iUnion
  intro rs
  by_cases hr : forestPopulationList n rs ∈ s
  · simp only [hr, true_and, Set.setOf_and]
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((hE _).preimage (measurable_const.prodMk measurable_snd))
  · simp only [hr, false_and, and_false, Set.setOf_false, MeasurableSet.empty]

end SRWTightness
