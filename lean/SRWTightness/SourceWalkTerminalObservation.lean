import SRWTightness.SourceWalkSuccessEvent

open Filter
open scoped Topology

namespace SRWTightness

/-- Actual annular observations identify the entire terminal list event on every finite-exit path. -/
theorem source_walk_terminal_observation :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (b : Site) (I : ℕ)
      (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      1 ≤ A * diskEnergyGapRatio ^ I →
      A * diskEnergyGapRatio ^ I ≤ sourceLowerRadius t / t ^ 6 →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ (ω : Sample), domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤ →
      ∀ r : FiniteExcursionRecord
        (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1),
      sourceActualForest t b _ ω = [r] → ∀ β : ℕ → GaussianCoefficientSpace,
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
      let k := sourceActualCount t b n ω
      let u := Real.sqrt (2 * (k : ℝ))
      let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
      let d := sourceLowerTime (sourceLowerRadius t)
      (finiteRecordLeaves n r, β) ∈ sourceTerminalListBridgeEvent t A γ b I z
        (geometricGWPopulation (finiteRecordPopulationList n r) n) ↔
      (sourceWalkObservation t A b I z k ω, β) ∈ sourceTerminalBridgeEvent t A I
        (sourceTerminalThreshold t u) q
        (Real.sqrt (d - sourceObservationTime t A I (I + 1))) d γ := by
  obtain ⟨T, hT⟩ := source_annular_local_observation
  filter_upwards [eventually_ge_atTop T, source_root_gw_horizon_large] with t ht hn
  intro A γ b I z ha hcut hblo hbhi ω hfin r hr β
  let ℓ := sourceRootDepth (Real.exp t) (sourceLowerRadius t)
  let n := ℓ - 1
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  have hℓ : 0 < ℓ := by dsimp [ℓ]; omega
  have hnℓ : n + 1 = ℓ := by omega
  have hpop : geometricGWPopulation (finiteRecordPopulationList n r) n =
      sourceActualCount t b n ω :=
    source_actual_forest_population t b K hℓ ω r hr n le_rfl
  have hraw : killedChildRecords (diskFinset (Real.exp t))
      (sourceEntranceDomain (sourceLowerRadius t) 1 (n + 1) b 0)
      (sourceExitDomain (sourceLowerRadius t) 1 (n + 1) b 0) 0
      (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 (n + 1) b)
        (sourceTreeExit (sourceLowerRadius t) 1 (n + 1) b) (wordOccupationMark K) n) ω = [r] := by
    simpa only [hnℓ, sourceActualForest] using hr
  have ho := hT t ht b (A * diskEnergyGapRatio ^ I) K ha hcut (by intro y hy; exact hy)
    hblo hbhi n hnℓ ω hfin r hraw (I + 1)
    (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
    (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) z
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi)
    (Real.sqrt (2 * (sourceActualCount t b n ω : ℝ)))
  dsimp only at ho
  rw [hpop] at ho
  dsimp only
  unfold sourceTerminalListBridgeEvent
  dsimp only
  simp only [Set.mem_preimage]
  rw [hpop]
  have hv : (fun i : Fin ((I + 1) + 1) ↦ normalizedObservation
      (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
      (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) z
      (sourceActualCount t b n ω) (sourceReferenceIntensity (sourceLowerRadius t) 14)
      (2 / Real.pi) (Real.sqrt (2 * (sourceActualCount t b n ω : ℝ)))
      (diskObservationIndex (I + 1) i)
      (terminalListSamples 0 (sourceActualCount t b n ω) (finiteRecordLeaves n r))) =
      sourceWalkObservation t A b I z (sourceActualCount t b n ω) ω := by
    funext i
    exact ho (diskObservationIndex (I + 1) i)
  rw [hv]

end SRWTightness
