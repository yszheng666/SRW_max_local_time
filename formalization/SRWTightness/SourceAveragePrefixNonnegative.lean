import SRWTightness.TimeGridPrefixNonnegative
import SRWTightness.SourcePairAverageIndex
import SRWTightness.SourceAveragePath

namespace SRWTightness

/-- A nonnegative correction on retained averages remains nonnegative on the actual prefix. -/
theorem sourceAveragePath_prefix_nonneg (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (x : Fin ((I + 1) + 1) → ℝ)
    (hx : ∀ j : Fin (I - i + 1), 2 * sourceObservationTime t A I (j.val + 1) ≤
      x (sourcePairAverageIndex I i j))
    (v : ℝ) (hv : 0 ≤ v) (hvtop : v ≤ sourceObservationTime t A I (I - i + 1)) :
    0 ≤ sourceAveragePath t A I x v := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  apply timeGridInterpolation_prefix_nonneg (sourceObservationTime t A I) _ (I + 1)
    (I - i + 1) (by omega) (by omega)
    (fun j hj ↦ by linarith [hg j (by omega)]) _ v
    (by simpa only [sourceObservationTime_zero] using hv) hvtop
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp only [observationMeshValue_zero, le_refl]
  · have hjpos : 0 < j := by omega
    have hjtop : j ≤ I + 1 := by omega
    simp only [observationMeshValue,
      dif_pos (show 0 < j ∧ j ≤ I + 1 from ⟨hjpos, hjtop⟩), Pi.sub_apply]
    simpa only [sourcePairAverageIndex, Fin.castSucc, Fin.castAdd, Fin.castLE] using
      sub_nonneg.mpr (hx ⟨j - 1, by omega⟩)

end SRWTightness
