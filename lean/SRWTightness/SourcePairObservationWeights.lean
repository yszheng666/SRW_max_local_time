import SRWTightness.PairObservationWeights
import SRWTightness.SourcePairObservationGeometry

namespace SRWTightness

/-- The retained source averages are ordered from the largest radius down to the pair node. -/
noncomputable def sourcePairAverageFamily (b : Site) (A : ℝ) (I i : ℕ) :
    Fin (I - i + 1) → Finset Site :=
  fun j ↦ translateFinset b (diskFinset (A * diskEnergyGapRatio ^ (I - j.val)))

/-- The actual pair vector meets the probability-weight hypotheses of the bounded tilt theorem. -/
theorem source_pair_observation_weights (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) :
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let w := pairObservationWeight D M (sourcePairAverageFamily b A I i) z y
    (∀ j x, 0 ≤ w j x) ∧ ∀ j, ∑ x, w j x = 1 := by
  have hgeometry (j : Fin (I - i + 1)) :=
    source_pair_observation_geometry b t A hA ht I hI (I - j.val) (Nat.sub_le _ _)
  have hMD := (source_pair_observation_geometry b t A hA ht I hI i hi).2.2.1
  apply pairObservationWeight_probability
  · intro j
    exact (hgeometry j).2.2.2.1
  · exact hMD
  · intro j
    refine ⟨b, ?_⟩
    change b ∈ translateFinset b (diskFinset (A * diskEnergyGapRatio ^ (I - j.val)))
    rw [mem_translateFinset_iff, sub_self]
    exact zero_mem_diskFinset _ (by linarith [(hgeometry j).1])

/-- The last retained average is exactly the selected pair observation radius. -/
theorem sourcePairAverageFamily_last (b : Site) (A : ℝ) (I i : ℕ) (hi : i ≤ I) :
    sourcePairAverageFamily b A I i (Fin.last (I - i)) =
      translateFinset b (diskFinset (A * diskEnergyGapRatio ^ i)) := by
  simp only [sourcePairAverageFamily, Fin.val_last, Nat.sub_sub_self hi]

end SRWTightness
