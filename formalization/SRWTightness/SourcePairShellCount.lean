import SRWTightness.LatticePairCount
import SRWTightness.SourcePairObservationIndex

namespace SRWTightness

/-- Candidate pairs belonging to the paper's geometric distance shell. -/
noncomputable def sourcePairShell (Z : Finset Site) (A : ℝ) (i : ℕ) : Finset (Site × Site) := by
  classical
  exact (Z.product Z).filter (fun p ↦
    4 * Real.sqrt (normSq (p.2 - p.1)) ≤ A * diskEnergyGapRatio ^ i ∧
    A * diskEnergyGapRatio ^ i ≤ 4 * diskEnergyGapRatio * Real.sqrt (normSq (p.2 - p.1)))

/-- Actual geometric shells inherit the quadratic spatial counting bound. -/
theorem source_pair_shell_card (hCount : LatticeDiskCountInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Finset Site) (A : ℝ) (i : ℕ),
      1 ≤ A * diskEnergyGapRatio ^ i →
      ((sourcePairShell Z A i).card : ℝ) ≤ C * Z.card * (A * diskEnergyGapRatio ^ i) ^ 2 := by
  classical
  obtain ⟨C, hC, hbound⟩ := lattice_nearby_pairs_quadratic hCount
  refine ⟨C, hC, ?_⟩
  intro Z A i ha
  have hsub : sourcePairShell Z A i ⊆ latticeNearbyPairs Z (A * diskEnergyGapRatio ^ i) := by
    intro p hp
    obtain ⟨hpZ, hpρ, _⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hpZ, ?_⟩
    have hρ := Real.sqrt_nonneg (normSq (p.2 - p.1))
    linarith
  have hc : ((sourcePairShell Z A i).card : ℝ) ≤
      (latticeNearbyPairs Z (A * diskEnergyGapRatio ^ i)).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (hbound Z _ ha)

end SRWTightness
