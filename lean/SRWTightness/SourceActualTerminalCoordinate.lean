import SRWTightness.SourceWalkTerminalObservation

open Filter
open scoped Topology

namespace SRWTightness

/-- Every coordinate in the first terminal disk uses the same actual root and count. -/
theorem source_actual_terminal_coordinate :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (b : Site) (I : ℕ),
      1 ≤ A * diskEnergyGapRatio ^ I →
      A * diskEnergyGapRatio ^ I ≤ sourceLowerRadius t / t ^ 6 →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ (ω : Sample), domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤ →
      ∀ r : FiniteExcursionRecord
        (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1),
      sourceActualForest t b _ ω = [r] →
      ∀ y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
      let k := sourceActualCount t b n ω
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let u := Real.sqrt (2 * (k : ℝ))
      normalizedMarkSum _ k α (2 / Real.pi) u y
        (terminalListSamples 0 k (finiteRecordLeaves n r)) =
      ((domainLocalTime (diskFinset (Real.exp t)) 0 y ω : ℝ) - α * k) /
        (u * Real.sqrt (α * (2 / Real.pi))) := by
  obtain ⟨T, hT⟩ := source_annular_local_observation
  filter_upwards [eventually_ge_atTop T, source_root_gw_horizon_large] with t ht hn
  intro A b I ha hcut hblo hbhi ω hfin r hr y
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
    hblo hbhi n hnℓ ω hfin r hraw 0 ∅ (fun i ↦ Fin.elim0 i) y
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi)
    (Real.sqrt (2 * (sourceActualCount t b n ω : ℝ))) none
  dsimp only at ho
  rw [hpop] at ho
  exact ho

end SRWTightness
