import SRWTightness.ActualFiniteRecordEvent
import SRWTightness.SourceTerminalListBridge
import SRWTightness.SourceGWBandWindows
import SRWTightness.SourceRootCoarseCounts

open MeasureTheory

namespace SRWTightness

/-- One actual root, the full coarse deficit band, and all measurable terminal bridge constraints. -/
def sourceCoarseTerminalForestEvent (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (n : ℕ) :
    Set (List (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n) ×
      (ℕ → GaussianCoefficientSpace)) :=
  {p | ∃ r, p.1 = [r] ∧
    finiteRecordPopulationList n r ∈ sourceGWCoarseBandEvent t n ∧
    (finiteRecordLeaves n r, p.2) ∈ sourceTerminalListBridgeEvent t A γ b I z
      (geometricGWPopulation (finiteRecordPopulationList n r) n)}

/-- The concrete forest success event is measurable, including its terminal population dependence. -/
theorem sourceCoarseTerminalForestEvent_measurable (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (n : ℕ)
    [MeasurableSpace (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSingletonClass (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSpace (List (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n))] :
    MeasurableSet (sourceCoarseTerminalForestEvent t A γ b I z n) := by
  letI := finiteExcursionRecord_countable
    (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n
  simp only [sourceCoarseTerminalForestEvent, Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro r
  by_cases hr : finiteRecordPopulationList n r ∈ sourceGWCoarseBandEvent t n
  · simp only [hr, true_and, Set.setOf_and]
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((sourceTerminalListBridgeEvent_measurable t A γ b I z _).preimage
        (measurable_const.prodMk measurable_snd))
  · simp only [hr, false_and, and_false, Set.setOf_false, MeasurableSet.empty]

/-- Every permitted forest has precisely one root, as required by the actual lower comparison. -/
theorem source_coarse_terminal_forest_length (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (n : ℕ)
    (p) (hp : p ∈ sourceCoarseTerminalForestEvent t A γ b I z n) : p.1.length = 1 := by
  obtain ⟨r, hr, _⟩ := hp
  rw [hr]
  rfl

/-- The concrete event supplies the entire coarse barrier needed for the vanishing error bound. -/
theorem source_coarse_terminal_forest_barrier (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (n : ℕ)
    (r) (y) (h : ([r], y) ∈ sourceCoarseTerminalForestEvent t A γ b I z n) :
    ∀ j : ℕ, 0 < j → j ≤ n →
      geometricGWHeight (finiteRecordPopulationList n r) j ≤
        4 + sourceBarrierSlope t * j -
          (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) := by
  obtain ⟨v, hv, hg, _⟩ := h
  have he : r = v := by simpa using hv
  subst v
  exact hg.1

/-- The decoded sample count is exactly the number of terminal leaves, so no missing marks are read. -/
theorem source_forest_terminal_sample_count {M : Type*} (n : ℕ)
    (r : FiniteExcursionRecord M n) :
    (finiteRecordLeaves n r).length =
      geometricGWPopulation (finiteRecordPopulationList n r) n := by
  rw [finiteRecordLeaves_length, finite_record_gw_population n r n le_rfl, Nat.sub_self]

end SRWTightness
