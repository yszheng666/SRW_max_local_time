import SRWTightness.SourceActualPairNodeCumulant
import SRWTightness.SourcePairObservationIndex

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- The late-pair cumulant at the first covering observation scale and original terminal count. -/
theorem source_late_pair_cumulant :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (b : Site),
      diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      ∀ (I : ℕ),
      (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) →
      ∀ (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      (z : Site) = b → A < Real.sqrt (normSq ((y : Site) - b)) →
      Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio) →
      ∃ i : ℕ, i ≤ I ∧
      4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i ∧
      A * diskEnergyGapRatio ^ i ≤ 4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)) ∧
      (∀ j : ℕ, j < i → A * diskEnergyGapRatio ^ j < 4 * Real.sqrt (normSq ((y : Site) - b))) ∧
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
  filter_upwards [source_actual_pair_node_cumulant] with t happ
  intro A b hA ht I hI z y hz hρ hcut
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  obtain ⟨i, hi, hlo, hhi, hmin⟩ := source_pair_observation_index A
    (Real.sqrt (normSq ((y : Site) - b))) I (by linarith) hρ hcut
  refine ⟨i, hi, hlo, hhi, hmin, ?_⟩
  intro ω hband
  exact happ A b hA ht I hI i hi z y hz (by linarith) hlo hhi ω hband

end SRWTightness
