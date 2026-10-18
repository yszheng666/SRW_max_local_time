import SRWTightness.PairObservationMean
import SRWTightness.SourcePairBrownianLower

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Actual Gaussian comparison means at all retained averages, including the discrete correction. -/
theorem source_pair_average_comparison_mean (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let R := Real.exp 1 * sourceLowerRadius t + 14
    let D := translateFinset b (diskFinset R)
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let F := fun a ↦ normalizedWeightedSum M k α (2 / Real.pi) u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y a)
    ∀ j : Fin (I - i + 1),
      (∑ l, pairObservationTilt (Fin.last (I - i)) l * covariance (F (.inl j)) (F l) μ) =
        2 * sourceObservationTime t A I (j.val + 1) +
          if j = Fin.last (I - i) then
            2 * geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) (I + 1)
              (sourcePairAverageIndex I i j) else 0 := by
  have hblock := source_pair_observation_covariance b t A hA ht I hI i hi
    z y hz hρ hlo u hu k hk
  have hmax := (source_pair_brownian_lower t A hA ht I hI i).1
  dsimp only at hblock ⊢
  intro j
  have hentry := congrFun (congrFun hblock (.inl j))
  simp_rw [hentry]
  exact pairObservation_average_mean _ _ _ _ hmax j

end SRWTightness
