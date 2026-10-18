import SRWTightness.SourceRecordSuccessProbability
import SRWTightness.SourceAnnularLocalObservation
import SRWTightness.SourceSuccessPositiveCount

namespace SRWTightness

/-- The actual chronological roots in the source disk-killed walk. -/
noncomputable def sourceActualForest (t : ℝ) (b : Site) (K : Finset Site) (ω : Sample) :
    List (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1)) :=
  let ℓ := sourceRootDepth (Real.exp t) (sourceLowerRadius t)
  killedChildRecords (diskFinset (Real.exp t))
    (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
    (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
    (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
      (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) (ℓ - 1)) ω

/-- The manuscript generation count, evaluated directly on the original walk. -/
noncomputable def sourceActualCount (t : ℝ) (b : Site) (j : ℕ) (ω : Sample) : ℕ :=
  sourceForwardRecordCount (sourceLowerRadius t) 1
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 j b (diskFinset (Real.exp t)) 0 ω

/-- The manuscript coarse barrier and deficit band using original-walk segment counts. -/
def sourceWalkCoarseBand (t : ℝ) (b : Site) (ω : Sample) : Prop :=
  let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
  (∀ j : ℕ, 0 < j → j ≤ n → Real.sqrt (2 * (sourceActualCount t b j ω : ℝ)) ≤
    4 + sourceBarrierSlope t * j -
      (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)) ∧
  sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) -
    Real.sqrt (2 * (sourceActualCount t b n ω : ℝ)) ∈
      Set.Icc (Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
        (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))

/-- Point and equilibrium-average observations of the original local times. -/
noncomputable def sourceWalkObservation (t A : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (k : ℕ) (ω : Sample) :
    Fin ((I + 1) + 1) → ℝ :=
  fun i ↦ domainLocalObservation
    (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
    (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) z (diskFinset (Real.exp t)) 0 ω k
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi)
    (Real.sqrt (2 * (k : ℝ))) (diskObservationIndex (I + 1) i)

/-- Original-walk success, with the measurable bridge version and explicit nonzero terminal count. -/
def sourceLocalTimeBridgeSuccessEvent (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) :
    Set (Sample × (ℕ → GaussianCoefficientSpace)) :=
  {p | let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
    let k := sourceActualCount t b n p.1
    let u := Real.sqrt (2 * (k : ℝ))
    let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
    let d := sourceLowerTime (sourceLowerRadius t)
    sourceActualCount t b 0 p.1 = 1 ∧ 0 < k ∧ sourceWalkCoarseBand t b p.1 ∧
    (sourceWalkObservation t A b I z k p.1, p.2) ∈
      sourceTerminalBridgeEvent t A I (sourceTerminalThreshold t u) q
        (Real.sqrt (d - sourceObservationTime t A I (I + 1))) d γ}

/-- The manuscript success event uses original local times and the continuous bridge constraint. -/
def sourceLocalTimeSuccessEvent (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) :
    Set (Sample × (ℕ → GaussianCoefficientSpace)) :=
  {p | let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
    let k := sourceActualCount t b n p.1
    let u := Real.sqrt (2 * (k : ℝ))
    let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
    let d := sourceLowerTime (sourceLowerRadius t)
    sourceActualCount t b 0 p.1 = 1 ∧ 0 < k ∧ sourceWalkCoarseBand t b p.1 ∧
    (sourceWalkObservation t A b I z k p.1, p.2) ∈
      sourceTerminalContinuousEvent t A I (sourceTerminalThreshold t u) q
        (Real.sqrt (d - sourceObservationTime t A I (I + 1))) d γ}

/-- Root-list length is precisely the manuscript root count, with no distributional assumption. -/
theorem source_actual_forest_length (t : ℝ) (b : Site) (K : Finset Site) (ω : Sample) :
    (sourceActualForest t b K ω).length = sourceActualCount t b 0 ω := by
  unfold sourceActualForest sourceActualCount
  rw [source_forward_root_count]
  simp only [killedChildRecords, wordChildRecords, List.length_map]

/-- Given one actual root, every permitted population coordinate is the original segment count. -/
theorem source_actual_forest_population (t : ℝ) (b : Site) (K : Finset Site)
    (hn : 0 < sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ω : Sample)
    (r : FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1))
    (hr : sourceActualForest t b K ω = [r]) (j : ℕ)
    (hj : j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) :
    geometricGWPopulation (finiteRecordPopulationList _ r) j = sourceActualCount t b j ω := by
  exact source_single_forest_gw_population (sourceLowerRadius t) 1 _ hn b
    (diskFinset (Real.exp t)) 0 (wordOccupationMark K) ω r hr j (by omega)

/-- The full coarse constraint agrees with the original-walk barrier on a single actual root. -/
theorem source_actual_forest_coarse_band (t : ℝ) (b : Site) (K : Finset Site)
    (hn : 0 < sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ω : Sample)
    (r : FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1))
    (hr : sourceActualForest t b K ω = [r]) :
    finiteRecordPopulationList _ r ∈ sourceGWCoarseBandEvent t
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ↔
        sourceWalkCoarseBand t b ω := by
  have hpop := source_actual_forest_population t b K hn ω r hr
  change ((∀ j, 0 < j → j ≤ _ → _ ≤ _) ∧ _) ↔ _
  simp only [geometricGWHeight, sourceWalkCoarseBand]
  rw [hpop _ le_rfl]
  constructor
  · rintro ⟨hbar, hband⟩
    refine ⟨?_, hband⟩
    intro j hj hjn
    simpa only [hpop j hjn] using hbar j hj hjn
  · rintro ⟨hbar, hband⟩
    refine ⟨?_, hband⟩
    intro j hj hjn
    simpa only [hpop j hjn] using hbar j hj hjn

end SRWTightness
