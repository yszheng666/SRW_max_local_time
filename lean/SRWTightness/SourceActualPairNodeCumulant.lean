import SRWTightness.SourcePairNodeCumulant
import SRWTightness.SourceWalkNormalization

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- The reference cumulant at the original walk terminal count and actual observation node. -/
theorem source_actual_pair_node_cumulant :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (b : Site),
      diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      ∀ (I : ℕ),
      (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) →
      ∀ (i : ℕ), i ≤ I →
      ∀ (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      (z : Site) = b → 1 ≤ Real.sqrt (normSq ((y : Site) - b)) →
      4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i →
      A * diskEnergyGapRatio ^ i ≤ 4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)) →
      ∀ (ω : Sample), sourceWalkCoarseBand t b ω →
      let k := sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ω
      let u := Real.sqrt (2 * (k : ℝ))
      let m := sourceLowerRadius t
      let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      let α := sourceReferenceIntensity m 14
      let F := normalizedMarkSum M k α (2 / Real.pi) u
      let S := normalizedEquilibriumAverage D M
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ i))) k α (2 / Real.pi) u
      |cgf ((2 : ℝ) • (F z + F y - S)) (markProductLaw D M α k) 1 -
        (4 * sourceLowerTime m - 2 * sourceObservationTime t A I (I - i + 1))| ≤
        1 + 4 * sourcePairVarianceError +
        4 * (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 +
          Real.log (4 * diskEnergyGapRatio)) + 1 / (2 / Real.pi) := by
  filter_upwards [source_pair_node_cumulant, source_walk_normalization_bounds] with t happ hnorm
  intro A b hA ht I hI i hi z y hz hρ hlo hhi ω hband
  let k := sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ω
  have hu := (hnorm b ω hband).1
  have hk : Real.sqrt (2 * (k : ℝ)) ^ 2 / 2 = (k : ℝ) := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  exact happ A b hA ht I hI i hi z y hz hρ hlo hhi _ hu k hk

end SRWTightness
