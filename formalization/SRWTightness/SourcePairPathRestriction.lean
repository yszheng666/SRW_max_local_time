import SRWTightness.TimeGridPrefixCongruence
import SRWTightness.SourceBridgedPath
import SRWTightness.SourcePairAverageIndex

namespace SRWTightness

/-- Retaining the pair averages preserves the whole source bridged path before the pair node. -/
theorem source_pair_bridged_prefix_congr (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (x y : Fin ((I + 1) + 1) → ℝ)
    (hxy : ∀ j : Fin (I - i + 1), x (sourcePairAverageIndex I i j) =
      y (sourcePairAverageIndex I i j))
    (ω : ℕ → GaussianCoefficientSpace) (v : ℝ)
    (hv : v ≤ sourceObservationTime t A I (I - i + 1)) :
    sourceBridgedPath t A I x ω v = sourceBridgedPath t A I y ω v := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  unfold sourceBridgedPath
  congr 1
  apply timeGridInterpolation_prefix_congr (sourceObservationTime t A I) _ _ (I + 1)
    (I - i + 1) (by omega) (fun j hj ↦ by linarith [hg j (by omega)]) _ v hv
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp only [observationMeshValue_zero]
  · have hjpos : 0 < j := by omega
    have hjtop : j ≤ I + 1 := by omega
    simp only [observationMeshValue, dif_pos (show 0 < j ∧ j ≤ I + 1 from ⟨hjpos, hjtop⟩), Pi.sub_apply]
    have hh := hxy ⟨j - 1, by omega⟩
    simpa only [sourcePairAverageIndex, Fin.castSucc, Fin.castAdd, Fin.castLE] using congrArg
      (fun a : ℝ ↦ a - 2 * sourceObservationTime t A I ((j - 1) + 1)) hh

end SRWTightness
