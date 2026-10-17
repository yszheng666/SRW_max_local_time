import SRWTightness.SourcePairShellCount

namespace SRWTightness

/-- The full late-distance range in the manuscript's ordered pair sum. -/
noncomputable def sourceLatePairs (Z : Finset Site) (A : ℝ) (I : ℕ) : Finset (Site × Site) := by
  classical
  exact (Z.product Z).filter (fun p ↦
    A < Real.sqrt (normSq (p.2 - p.1)) ∧
    Real.sqrt (normSq (p.2 - p.1)) ≤ A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio))

/-- Every actual late-distance pair belongs to a retained shell, with its first-cover property. -/
theorem source_late_pair_shell_cover (Z : Finset Site) (A : ℝ) (I : ℕ) (hA : 0 < A)
    (p : Site × Site) (hp : p ∈ sourceLatePairs Z A I) :
    ∃ i : ℕ, i ≤ I ∧ p ∈ sourcePairShell Z A i ∧
      ∀ j : ℕ, j < i → A * diskEnergyGapRatio ^ j < 4 * Real.sqrt (normSq (p.2 - p.1)) := by
  classical
  obtain ⟨hpZ, hlo, hhi⟩ := Finset.mem_filter.mp hp
  obtain ⟨i, hi, hil, hiu, hmin⟩ := source_pair_observation_index A _ I hA hlo hhi
  exact ⟨i, hi, Finset.mem_filter.mpr ⟨hpZ, hil, hiu⟩, hmin⟩

end SRWTightness
