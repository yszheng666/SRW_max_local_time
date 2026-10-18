import SRWTightness.SourcePairWindowOriginal

namespace SRWTightness

/-- The actual pair mark vector agrees with the old full source vector on every retained average. -/
theorem source_pair_reference_coordinates (b : Site) (A : ℝ) (I i : ℕ)
    (D M : Finset Site) (z y : M) (k : ℕ) (α g u : ℝ) (Y : MarkSamples M k)
    (j : Fin (I - i + 1)) :
    normalizedWeightedSum M k α g u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y (.inl j)) Y =
    normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
      z k α g u (diskObservationIndex (I + 1) (sourcePairAverageIndex I i j)) Y := by
  simpa only [pairObservationWeight, normalizedWeightedSum_observationWeight,
    normalizedObservation] using
    (congrFun (sourcePairAverageIndex_observation b A I i D M z k α g u j) Y).symm

end SRWTightness
