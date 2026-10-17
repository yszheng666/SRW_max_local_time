import SRWTightness.SourceCenteredSuccessCount
import SRWTightness.SourceWalkSuccessIdentification

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SRWTightness

/-- The coarse event of source (5.4), using actual original-walk traversal counts. -/
def sourceOriginalCoarseEvent (t : ℝ) (b : Site) : Set Sample :=
  {ω | sourceActualCount t b 0 ω = 1 ∧
    ∀ j : ℕ, 0 < j → j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 →
      Real.sqrt (2 * (sourceActualCount t b j ω : ℝ)) ≤
        4 + sourceBarrierSlope t * j -
          (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)}

/-- The actual terminal deficit in source (5.5). -/
noncomputable def sourceOriginalDeficit (t : ℝ) (b : Site) (ω : Sample) : ℝ :=
  sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) -
    Real.sqrt (2 * (sourceActualCount t b
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ω : ℝ))

/-- The original coarse event is exactly one root and every source coarse inequality. -/
theorem source_original_coarse_event (t : ℝ) (b : Site) (ω : Sample) :
    ω ∈ sourceOriginalCoarseEvent t b ↔ sourceActualCount t b 0 ω = 1 ∧
      ∀ j : ℕ, 0 < j → j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 →
        Real.sqrt (2 * (sourceActualCount t b j ω : ℝ)) ≤
          4 + sourceBarrierSlope t * j -
            (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) := Iff.rfl

/-- The deficit is x_star minus the actual square-root terminal population. -/
theorem source_original_deficit_formula (t : ℝ) (b : Site) (ω : Sample) :
    sourceOriginalDeficit t b ω = sourceTerminalRoot t 0 -
      Real.sqrt (2 * (sourceActualCount t b
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ω : ℝ)) := by
  simp [sourceOriginalDeficit, sourceTerminalRoot]

/-- The actual success event is the literal intersection in source (5.15), including k>0. -/
theorem source_original_success_decomposition (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (p : Sample × (ℕ → GaussianCoefficientSpace)) :
    p ∈ sourceLocalTimeSuccessEvent t A γ b I z ↔
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
      let k := sourceActualCount t b n p.1
      let u := Real.sqrt (2 * (k : ℝ))
      let d := sourceLowerTime (sourceLowerRadius t)
      p.1 ∈ sourceOriginalCoarseEvent t b ∧ 0 < k ∧
      sourceOriginalDeficit t b p.1 ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) ∧
      (sourceWalkObservation t A b I z k p.1, p.2) ∈
        sourceTerminalContinuousEvent t A I (sourceTerminalThreshold t u)
          (sourceOriginalDeficit t b p.1)
          (Real.sqrt (d - sourceObservationTime t A I (I + 1))) d γ := by
  simp only [sourceLocalTimeSuccessEvent, sourceWalkCoarseBand, sourceOriginalCoarseEvent,
    sourceOriginalDeficit, Set.mem_setOf_eq]
  tauto

/-- A zero terminal population gives the empty success event, pathwise. -/
theorem source_original_success_zero_terminal (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (p : Sample × (ℕ → GaussianCoefficientSpace))
    (hk : sourceActualCount t b
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) p.1 = 0) :
    p ∉ sourceLocalTimeSuccessEvent t A γ b I z := by
  intro hp
  exact (Nat.ne_of_gt hp.2.1) hk

/-- The implemented count is the sum of the original continuous success indicators. -/
theorem source_original_success_count (R A γ : ℝ)
    (I : sourceCandidateAnnulus R → ℕ)
    (z : ∀ b : sourceCandidateAnnulus R,
      translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b)))
    (p : Sample × (Site → ℕ → GaussianCoefficientSpace)) :
    sourceSuccessCount R A γ I z p =
      ∑ b : sourceCandidateAnnulus R,
        (if sourceSiteProjection b p ∈ sourceLocalTimeSuccessEvent
          (Real.log R) A γ b (I b) (z b) then (1 : ℝ) else 0) := by
  unfold sourceSuccessCount sourceSiteSuccessEvent
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hp : sourceSiteProjection b p ∈ sourceLocalTimeSuccessEvent
      (Real.log R) A γ b (I b) (z b)
  · simp [hp]
  · simp [hp]

end SRWTightness
