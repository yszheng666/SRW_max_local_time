import SRWTightness.SourcePairTiltApproximation
import SRWTightness.SourcePairRadiusMargin
import SRWTightness.SourcePairObservationIndex
import SRWTightness.SourceWalkNormalization

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology

namespace SRWTightness

/-- The late-pair CLT at the first covering node and original walk terminal count. -/
theorem source_late_pair_tilt_approximation
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (b : Site),
      diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      sourcePairLogMargin + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A →
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
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let F := fun j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j)
    let β := pairObservationTilt (Fin.last (I - i))
    let S := normalizedEquilibriumAverage D M
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ i))) k α (2 / Real.pi) u
    let G := normalizedMarkSum M k α (2 / Real.pi) u
    let ρ := μ.tilted (fun Y ↦ 2 * (G z Y + G y Y - S Y))
    let Sigma : Matrix (PairObservationIndex (I - i + 1)) _ ℝ :=
      fun j l ↦ covariance (F j) (F l) μ
    let target := fun j ↦ ∑ l, β l * Sigma j l
    IsProbabilityMeasure ρ ∧ Sigma.PosDef ∧
      (∀ (s : Set (PairObservationIndex (I - i + 1) → ℝ)),
        MeasurableSet s → Convex ℝ s →
        |(ρ.map (fun Y j ↦ F j Y)).real s -
          (gaussianMeanCoordinateLaw target Sigma).real s| ≤
        sourceTiltApproximationConstant 1 6 (2 * sourceObservationDimensionConstant) (1 / 16) *
          sourceLowerTime (sourceLowerRadius t) ^ 5 / t) ∧
      (∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
        (s : Set ((PairObservationIndex (I - i + 1) → ℝ) × Ξ)),
        MeasurableSet s → (∀ᵐ y ∂ν, Convex ℝ ((fun x ↦ (x, y)) ⁻¹' s)) →
        |((ρ.map (fun Y j ↦ F j Y)).prod ν).real s -
          ((gaussianMeanCoordinateLaw target Sigma).prod ν).real s| ≤
        sourceTiltApproximationConstant 1 6 (2 * sourceObservationDimensionConstant) (1 / 16) *
          sourceLowerTime (sourceLowerRadius t) ^ 5 / t) := by
  filter_upwards [source_pair_tilt_approximation hBE, source_walk_normalization_bounds]
    with t happ hnorm
  intro A b hA ht hmargin I hI z y hz hρ hcut
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  obtain ⟨i, hi, hlo, hhi, hmin⟩ := source_pair_observation_index A
    (Real.sqrt (normSq ((y : Site) - b))) I (by linarith) hρ hcut
  have hm := source_pair_radius_margin A hA hmargin
  refine ⟨i, hi, hlo, hhi, hmin, ?_⟩
  intro ω hband
  let k := sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ω
  have hu := (hnorm b ω hband).1
  have hk : Real.sqrt (2 * (k : ℝ)) ^ 2 / 2 = (k : ℝ) := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have h := happ b A hA ht hm.1 hm.2 I hI i hi z y hz (by linarith)
    hlo hhi _ hu k hk
  dsimp only at h ⊢
  simpa only [pairObservationTilt_statistic, sourcePairAverageFamily_last b A I i hi] using h

end SRWTightness
