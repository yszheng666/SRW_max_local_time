import SRWTightness.PairObservationWeights
import SRWTightness.SourceObservationDimension

namespace SRWTightness

/-- The retained averages plus both sites obey a dimension bound independent of the pair node. -/
theorem source_pair_observation_dimension (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) :
    (Fintype.card (PairObservationIndex (I - i + 1)) : ℝ) ≤
      (2 * sourceObservationDimensionConstant) * sourceLowerTime (sourceLowerRadius t) := by
  have hd := source_observation_dimension t A hA ht I hI
  have hn : Fintype.card (PairObservationIndex (I - i + 1)) ≤
      2 * Fintype.card (Fin ((I + 1) + 1)) := by
    simp only [PairObservationIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
    omega
  have hr : (Fintype.card (PairObservationIndex (I - i + 1)) : ℝ) ≤
      2 * (Fintype.card (Fin ((I + 1) + 1)) : ℝ) := by exact_mod_cast hn
  nlinarith

end SRWTightness
