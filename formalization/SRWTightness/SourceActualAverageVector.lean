import SRWTightness.SourceActualTerminalCoordinate

open Filter

namespace SRWTightness

/-- Coordinate recovery also recovers every equilibrium average with the same centering. -/
theorem normalizedObservation_domain_eq_of_sites {q : ℕ} (Dref K : Finset Site)
    (family : Fin q → Finset Site) (z : K) (D : Finset Site) (x : Site) (ω : Sample)
    (k : ℕ) (α g u : ℝ) (Y : MarkSamples K k)
    (hsite : ∀ y : K, normalizedMarkSum K k α g u y Y =
      ((domainLocalTime D x y ω : ℝ) - α * k) / (u * Real.sqrt (α * g)))
    (j : Option (Fin q)) :
    normalizedObservation Dref K family z k α g u j Y =
      domainLocalObservation Dref K family z D x ω k α g u j := by
  cases j with
  | none => exact hsite z
  | some j =>
    simp only [normalizedObservation, normalizedEquilibriumAverage, normalizedWeightedSum,
      domainLocalObservation]
    apply Finset.sum_congr rfl
    intro y _
    rw [hsite y]

/-- The full decoded terminal vector is the original walk's average observation vector. -/
theorem source_actual_average_vector :
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
      ∀ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
      let k := sourceActualCount t b n ω
      let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let u := Real.sqrt (2 * (k : ℝ))
      (fun j : Fin ((I + 1) + 1) ↦ normalizedObservation D M
        (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) z k α (2 / Real.pi) u
        (diskObservationIndex (I + 1) j)
        (terminalListSamples 0 k (finiteRecordLeaves n r))) =
      sourceWalkObservation t A b I z k ω := by
  filter_upwards [source_actual_terminal_coordinate] with t ht
  intro A b I ha hcut hblo hbhi ω hfin r hr z
  dsimp only
  funext j
  exact normalizedObservation_domain_eq_of_sites _ _ _ _ _ _ _ _ _ _ _ _
    (ht A b I ha hcut hblo hbhi ω hfin r hr) (diskObservationIndex (I + 1) j)

end SRWTightness
