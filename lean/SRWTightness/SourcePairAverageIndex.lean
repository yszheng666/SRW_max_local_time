import SRWTightness.SourcePairObservationWeights

namespace SRWTightness

/-- A retained pair average occupies the same coordinate as in the full source observation vector. -/
def sourcePairAverageIndex (I i : ℕ) (j : Fin (I - i + 1)) : Fin ((I + 1) + 1) :=
  (⟨j.val, by omega⟩ : Fin (I + 1)).castSucc

/-- Restricting the old source vector gives the actual retained average, with no new observation law. -/
theorem sourcePairAverageIndex_observation (b : Site) (A : ℝ) (I i : ℕ)
    (D M : Finset Site) (z : M) (k : ℕ) (α g u : ℝ) (j : Fin (I - i + 1)) :
    normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
      z k α g u (diskObservationIndex (I + 1) (sourcePairAverageIndex I i j)) =
    normalizedEquilibriumAverage D M (sourcePairAverageFamily b A I i j) k α g u := by
  simp only [sourcePairAverageIndex, diskObservationIndex_castSucc, normalizedObservation,
    geometricDiskFamily, Fin.val_rev, sourcePairAverageFamily]
  rw [show I + 1 - (j.val + 1) = I - j.val by omega]

end SRWTightness
