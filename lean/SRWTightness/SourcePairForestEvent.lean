import SRWTightness.ActualFiniteRecordEvent
import SRWTightness.SourcePairListEvent
import SRWTightness.SourceGWBandWindows
import SRWTightness.SourceRootCoarseCounts

open MeasureTheory

namespace SRWTightness

/-- One actual root, the full coarse deficit band, and the measurable pair-prefix constraints. -/
def sourcePairForestEvent (t A : ℝ) (b : Site) (I i : ℕ)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (f : ℝ) (n : ℕ) :
    Set (List (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n) ×
      (ℕ → GaussianCoefficientSpace)) :=
  {p | ∃ r, p.1 = [r] ∧
    finiteRecordPopulationList n r ∈ sourceGWCoarseBandEvent t n ∧
    (finiteRecordLeaves n r, p.2) ∈ sourcePairListEvent t A b I i z y
      (geometricGWPopulation (finiteRecordPopulationList n r) n) f}

/-- The concrete pair forest event is measurable, including its terminal population dependence. -/
theorem sourcePairForestEvent_measurable (t A : ℝ) (b : Site) (I i : ℕ)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (f : ℝ) (n : ℕ)
    [MeasurableSpace (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSingletonClass (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSpace (List (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n))] :
    MeasurableSet (sourcePairForestEvent t A b I i z y f n) := by
  letI := finiteExcursionRecord_countable
    (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n
  simp only [sourcePairForestEvent, Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro r
  by_cases hr : finiteRecordPopulationList n r ∈ sourceGWCoarseBandEvent t n
  · simp only [hr, true_and, Set.setOf_and]
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((sourcePairListEvent_measurable t A b I i z y _ f).preimage
        (measurable_const.prodMk measurable_snd))
  · simp only [hr, false_and, and_false, Set.setOf_false, MeasurableSet.empty]

/-- Every permitted forest has precisely one root, as required by the actual lower comparison. -/
theorem source_pair_forest_length (t A : ℝ) (b : Site) (I i : ℕ)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (f : ℝ) (n : ℕ)
    (p) (hp : p ∈ sourcePairForestEvent t A b I i z y f n) : p.1.length = 1 := by
  obtain ⟨r, hr, _⟩ := hp
  rw [hr]
  rfl

/-- The concrete event supplies the entire coarse barrier needed for the vanishing error bound. -/
theorem source_pair_forest_barrier (t A : ℝ) (b : Site) (I i : ℕ)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (f : ℝ) (n : ℕ)
    (r) (β) (h : ([r], β) ∈ sourcePairForestEvent t A b I i z y f n) :
    ∀ j : ℕ, 0 < j → j ≤ n →
      geometricGWHeight (finiteRecordPopulationList n r) j ≤
        4 + sourceBarrierSlope t * j -
          (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) := by
  obtain ⟨v, hv, hg, _⟩ := h
  have he : r = v := by simpa using hv
  subst v
  exact hg.1

end SRWTightness
