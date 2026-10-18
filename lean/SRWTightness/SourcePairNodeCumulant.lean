import SRWTightness.SourcePairCumulant
import SRWTightness.SourcePairObservationGeometry

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- The pair cumulant at an actual source observation node, with all support and capacity conditions discharged. -/
theorem source_pair_node_cumulant :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (b : Site),
      diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      ∀ (I : ℕ),
      (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) →
      ∀ (i : ℕ), i ≤ I →
      ∀ (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      (z : Site) = b → 1 ≤ Real.sqrt (normSq ((y : Site) - b)) →
      4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i →
      A * diskEnergyGapRatio ^ i ≤ 4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)) →
      ∀ (u : ℝ), t ≤ u → ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
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
  filter_upwards [source_pair_cumulant (4 * diskEnergyGapRatio)] with t happ
  intro A b hA ht I hI i hi z y hz hρ hlo hhi u hu k hk
  obtain ⟨ha, hma, hMD, hKM, hcap⟩ := source_pair_observation_geometry b t A hA ht I hI i hi
  have hh := happ b (A * diskEnergyGapRatio ^ i)
    (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    hma hMD hKM hcap z y hz hρ hlo hhi u hu k hk
  dsimp only at hh ⊢
  rw [source_observation_time_at_radius b t A I i hi]
  exact hh

end SRWTightness
