import SRWTightness.SourcePairCovarianceLower
import SRWTightness.SourcePairObservationDimension
import SRWTightness.SourceBoundedTiltApproximation

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology

namespace SRWTightness

/-- The actual retained pair vector satisfies the external-CLT Gaussian approximation. -/
theorem source_pair_tilt_approximation
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (A : ℝ)
      (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : 4 * sourcePairResidualError + 3 + sourceEquilibriumTimeError +
      sourceLowerTimeError ≤ Real.log A)
    (hsmall : (diskEquilibriumWeightConstant / A) / (2 / Real.pi) ≤ 1 / 16)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : t ≤ u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)),
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let F := fun j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j)
    let β := pairObservationTilt (Fin.last (I - i))
    let ρ := μ.tilted (fun Y ↦ ∑ j, β j * F j Y)
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
  have happ := source_bounded_tilt_approximation hBE 1 6
    (2 * sourceObservationDimensionConstant) (1 / 16)
    (by norm_num) (by norm_num)
    (mul_pos (by norm_num) sourceObservationDimensionConstant_pos) (by norm_num)
  filter_upwards [happ, eventually_gt_atTop (0 : ℝ)] with t happ ht0
  intro b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi u hu k hk
  have hg := source_pair_observation_geometry b t A hA ht I hI i hi
  have hw := source_pair_observation_weights b t A hA ht I hI i hi z y
  have hd := source_pair_observation_dimension t A hA ht I hI i
  have hl := source_pair_covariance_lower b t A hA ht hlog hsmall I hI i hi
    z y hz hρ hlo hhi u (ht0.trans_le hu) k hk
  have h := happ (PairObservationIndex (I - i + 1)) b
    (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) hg.2.2.1 hg.2.2.2.2 hd
    u (by simpa only [one_mul] using hu) k hk _ hw.1 hw.2
    (pairObservationTilt (Fin.last (I - i))) (pairObservationTilt_l1 _) hl
  exact ⟨h.1, h.2.1, h.2.2.2⟩

/-- The actual pair approximation error is little-o of the inverse square of source time. -/
theorem source_pair_tilt_error_scaled_tendsto_zero :
    Tendsto (fun t : ℝ ↦ sourceLowerTime (sourceLowerRadius t) ^ (2 : ℝ) *
      (sourceTiltApproximationConstant 1 6 (2 * sourceObservationDimensionConstant) (1 / 16) *
        sourceLowerTime (sourceLowerRadius t) ^ 5 / t)) atTop (𝓝 0) := by
  exact source_tilt_approximation_scaled_tendsto_zero 1 6
    (2 * sourceObservationDimensionConstant) (1 / 16) 2
    (by norm_num) (by norm_num)
    (mul_pos (by norm_num) sourceObservationDimensionConstant_pos) (by norm_num)

end SRWTightness
