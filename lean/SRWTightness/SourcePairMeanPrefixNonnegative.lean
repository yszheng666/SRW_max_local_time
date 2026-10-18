import SRWTightness.SourcePairAverageComparisonMean
import SRWTightness.SourceAveragePrefixNonnegative
import SRWTightness.PairObservationExtension
import SRWTightness.SourcePairErrorBounds

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual Gaussian comparison mean only tightens the flat prefix restriction. -/
theorem source_pair_comparison_mean_prefix_nonneg (b : Site) (t A : ℝ)
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
    let mean := fun j ↦ ∑ l, pairObservationTilt (Fin.last (I - i)) l * covariance (F j) (F l) μ
    ∀ v : ℝ, 0 ≤ v → v ≤ sourceObservationTime t A I (I - i + 1) →
      0 ≤ sourceAveragePath t A I (pairObservationExtension I i mean) v := by
  have hmean := source_pair_average_comparison_mean b t A hA ht I hI i hi
    z y hz hρ hlo u hu k hk
  have he := source_pair_error_bounds b t A hA ht I hI i
  dsimp only at hmean he ⊢
  intro v hv hvtop
  apply sourceAveragePath_prefix_nonneg t A I i hA ht hI _ _ v hv hvtop
  intro j
  rw [pairObservationExtension_retained, hmean j]
  have hej := he.1 (.inl j)
  change 0 ≤ geometricDiskPointError b A (Real.exp 1 * sourceLowerRadius t + 14)
    diskEnergyGapRatio (2 / Real.pi) (I + 1) (sourcePairAverageIndex I i j) at hej
  split <;> linarith

end SRWTightness
