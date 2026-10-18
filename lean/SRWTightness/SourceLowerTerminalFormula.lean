import SRWTightness.SourceWalkContinuousSuccess
import SRWTightness.SourceTerminalThreshold

open scoped BigOperators

namespace SRWTightness

/-- The last source observation is exactly the original normalized point occupation. -/
theorem source_walk_point_observation_formula (t A : ℝ) (b : Site) (I k : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (ω : Sample) :
    sourceWalkObservation t A b I z k ω (Fin.last (I + 1)) =
      ((domainLocalTime (diskFinset (Real.exp t)) 0 z ω : ℝ) -
        sourceReferenceIntensity (sourceLowerRadius t) 14 * k) /
        (Real.sqrt (2 * (k : ℝ)) *
          Real.sqrt (sourceReferenceIntensity (sourceLowerRadius t) 14 * (2 / Real.pi))) := by
  simp only [sourceWalkObservation, diskObservationIndex_last, domainLocalObservation]

/-- The next-to-last observation is exactly the original innermost equilibrium average. -/
theorem source_walk_innermost_average_formula (t A : ℝ) (b : Site) (I k : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (ω : Sample) :
    sourceWalkObservation t A b I z k ω ⟨I, by omega⟩ =
      ∑ y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
        equilibriumWeight (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
          (translateFinset b (diskFinset A)) y *
          (((domainLocalTime (diskFinset (Real.exp t)) 0 y ω : ℝ) -
            sourceReferenceIntensity (sourceLowerRadius t) 14 * k) /
            (Real.sqrt (2 * (k : ℝ)) *
              Real.sqrt (sourceReferenceIntensity (sourceLowerRadius t) 14 * (2 / Real.pi)))) := by
  have hi : diskObservationIndex (I + 1) (⟨I, by omega⟩ : Fin ((I + 1) + 1)) =
      some (0 : Fin (I + 1)) := by
    change diskObservationIndex (I + 1) (Fin.last I).castSucc = _
    rw [diskObservationIndex_castSucc]
    simp
  simp only [sourceWalkObservation, hi, domainLocalObservation, geometricDiskFamily,
    Fin.val_zero, pow_zero, mul_one]

/-- The terminal normalized integer threshold is the literal original squared-centering cutoff. -/
theorem source_walk_terminal_cutoff_formula (t : ℝ) (k : ℕ) :
    sourceTerminalThreshold t (Real.sqrt (2 * (k : ℝ))) =
      ((Nat.ceil (diskCenter (Real.exp t) ^ 2) : ℝ) -
        sourceReferenceIntensity (sourceLowerRadius t) 14 * k) /
        (Real.sqrt (2 * (k : ℝ)) *
          Real.sqrt (sourceReferenceIntensity (sourceLowerRadius t) 14 * (2 / Real.pi))) := by
  have hu : (Real.sqrt (2 * (k : ℝ))) ^ 2 / 2 = (k : ℝ) := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  rw [sourceTerminalThreshold_visit_formula t _ k hu]
  have hk := sourceTerminalVisitCutoff_at_radius (Real.exp t)
  rw [Real.log_exp] at hk
  rw [hk]

/-- The actual terminal constraint has precisely the two windows and all continuous barrier
tests. -/
theorem source_walk_terminal_event_formula (t A γ : ℝ) (b : Site) (I k : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (ω : Sample) (β : ℕ → GaussianCoefficientSpace) :
    let u := Real.sqrt (2 * (k : ℝ))
    let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
    let d := sourceLowerTime (sourceLowerRadius t)
    let v₀ := sourceObservationTime t A I (I + 1)
    let aStar := Real.sqrt (d - v₀)
    let F := sourceWalkObservation t A b I z k ω
    let At := ((Nat.ceil (diskCenter (Real.exp t) ^ 2) : ℝ) -
      sourceReferenceIntensity (sourceLowerRadius t) 14 * k) /
      (u * Real.sqrt (sourceReferenceIntensity (sourceLowerRadius t) 14 * (2 / Real.pi)))
    (F, β) ∈ sourceTerminalContinuousEvent t A I
        (sourceTerminalThreshold t u) q aStar d γ ↔
      At ≤ F (Fin.last (I + 1)) ∧ F (Fin.last (I + 1)) ≤ At + 1 ∧
      q - aStar - 1 ≤ F ⟨I, by omega⟩ - 2 * v₀ ∧
      F ⟨I, by omega⟩ - 2 * v₀ ≤ q - aStar ∧
      ∀ v : ℝ, 0 ≤ v → v ≤ v₀ →
        sourceBridgedPath t A I F β v ≤ q - (d - v) ^ γ := by
  dsimp only
  rw [source_walk_terminal_cutoff_formula]
  rfl

end SRWTightness
