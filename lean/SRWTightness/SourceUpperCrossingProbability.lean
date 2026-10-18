import SRWTightness.SourceUpperAllLevelSum
import SRWTightness.SourceUpperCrossingEvent
import Mathlib.Order.LiminfLimsup

open Filter MeasureTheory

namespace SRWTightness

/-- The complete actual crossing event has a uniform exponential excess-height bound. -/
theorem source_upper_crossing_probability (hinput : PotentialKernelAsymptoticInput)
    (hScale : ExponentialFloorScaleInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      pathLaw.real (sourceUpperCrossingEvent t s) ≤ C * Real.exp (-3 * s / 2) := by
  obtain ⟨C, hC, hsum⟩ := source_upper_all_level_sum hinput hScale
  refine ⟨C, hC, ?_⟩
  filter_upwards [source_upper_crossing_union_bound, hsum] with t hu hs
  intro s hs0 hslog
  exact (hu s).trans (hs s hs0 hslog)

/-- The actual source crossing event parameterized by the outer radius R. -/
def sourceUpperCrossingAtRadius (R s : ℝ) : Set Sample := sourceUpperCrossingEvent (Real.log R) s

/-- For positive radii this is precisely the manuscript half-disk crossing event. -/
theorem mem_sourceUpperCrossingAtRadius (R s : ℝ) (hR : 0 < R) (ω : Sample) :
    ω ∈ sourceUpperCrossingAtRadius R s ↔
      ∃ x ∈ diskFinset (R / 2), ∃ j : ℕ, j ≤ sourceUpperCoarseDepth (Real.log R) ∧
        sourceUpperBarrier (Real.log R) s j <
          Real.sqrt (2 * (sourceUpperTraversalCount (Real.log R) j x ω : ℝ)) := by
  simp [sourceUpperCrossingAtRadius, sourceUpperCrossingEvent, Real.exp_log hR,
    Finset.mem_range, Nat.lt_succ_iff]

/-- The radius-parameterized crossing event is measurable for every radius. -/
theorem measurableSet_sourceUpperCrossingAtRadius (R s : ℝ) :
    MeasurableSet (sourceUpperCrossingAtRadius R s) :=
  measurableSet_sourceUpperCrossingEvent _ _

/-- The source crossing probability obeys the eventual bound for each fixed nonnegative height. -/
theorem source_upper_crossing_probability_radius (hinput : PotentialKernelAsymptoticInput)
    (hScale : ExponentialFloorScaleInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s → ∀ᶠ R : ℝ in atTop,
      pathLaw.real (sourceUpperCrossingAtRadius R s) ≤ C * Real.exp (-3 * s / 2) := by
  obtain ⟨C, hC, hbound⟩ := source_upper_crossing_probability hinput hScale
  refine ⟨C, hC, ?_⟩
  intro s hs
  have ht : ∀ᶠ t : ℝ in atTop,
      pathLaw.real (sourceUpperCrossingEvent t s) ≤ C * Real.exp (-3 * s / 2) := by
    filter_upwards [hbound, Real.tendsto_log_atTop.eventually (eventually_ge_atTop s)]
      with t hb hlog
    exact hb s hs hlog
  exact Real.tendsto_log_atTop.eventually ht

/-- Equation (4.18): the full actual SRW barrier-crossing probability has the stated limsup. -/
theorem source_upper_crossing_limsup (hinput : PotentialKernelAsymptoticInput)
    (hScale : ExponentialFloorScaleInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s →
      (limsup (fun R : ℝ ↦ pathLaw.real (sourceUpperCrossingAtRadius R s)) atTop) ≤
        C * Real.exp (-3 * s / 2) := by
  obtain ⟨C, hC, hbound⟩ := source_upper_crossing_probability_radius hinput hScale
  refine ⟨C, hC, ?_⟩
  intro s hs
  exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun R ↦ measureReal_nonneg))
    (hbound s hs)

end SRWTightness
