import SRWTightness.SourcePairMarkProbability
import SRWTightness.SourceGWWeightedBandUpper

open MeasureTheory ProbabilityTheory Filter

namespace SRWTightness

/-- Integrating the actual pair reference probabilities over the full coarse deficit band. -/
theorem source_pair_reference_band_upper
    (hUpper : GWBarrierUpperInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hGaussian : GaussianEndpointResidualInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (A : ℝ)
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
    (f : ℝ) (hf : 0 ≤ f)
    (hv : sourceLowerTime (sourceLowerRadius t) / 2 ≤
      sourceObservationTime t A I (I - i + 1)),
    let d := sourceLowerTime (sourceLowerRadius t)
    let h := d - sourceObservationTime t A I (I - i + 1)
    let L := (sourceCoarseGeneration t).toNat
    (∫ r in sourceGWCoarseBandEvent t L,
      sourcePairMarkProbability t A b I i z y (geometricGWPopulation r L) f
        ∂geometricGWRecordLaw 1 L) ≤
      C * ((f + 1) / h) * Real.exp (-2 * t - 2 * h - 2 * f) := by
  obtain ⟨G, hG, hband⟩ := source_gw_weighted_band_upper hUpper
  refine ⟨G * sourcePairReferenceUpperConstant, by
    exact mul_pos hG sourcePairReferenceUpperConstant_pos, ?_⟩
  filter_upwards [hband, source_pair_mark_probability_bound hKernel hGaussian hBE]
    with t hband happ
  intro b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi f hf hv
  dsimp only
  let d := sourceLowerTime (sourceLowerRadius t)
  let h := d - sourceObservationTime t A I (I - i + 1)
  let L := (sourceCoarseGeneration t).toNat
  let P := fun r ↦ sourcePairMarkProbability t A b I i z y (geometricGWPopulation r L) f
  let a := sourcePairReferenceUpperConstant * ((f + 1) / h) * Real.exp (-2 * h - 2 * f)
  have hh : 0 < h := (source_pair_residual_time b t A sourcePairResidualError hA ht
    (le_max_left _ _) (by linarith) I hI i hi).1
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (mul_nonneg sourcePairReferenceUpperConstant_pos.le
      (div_nonneg (by linarith) hh.le)) (Real.exp_nonneg _)
  have hg := source_pair_observation_geometry b t A hA ht I hI i hi
  have hs := sourceScaleThreshold_conditions t A
    (diskGaussianMinimumRadius_ge_four.trans (diskPointGaussianMinimumRadius_ge_base.trans hA))
    ((le_max_left _ _).trans ht)
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith [hs.2.2.1])).1
  have hP : ∀ r, P r ∈ Set.Icc (0 : ℝ) 1 := fun r ↦
    source_pair_mark_probability_mem t A b I i z y _ f hα.le hg.2.2.2.2
  have hpoint : ∀ r ∈ sourceGWCoarseBandEvent t L,
      P r ≤ a * (Real.exp (-2 * d - 2 *
        (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L)) / d) := by
    intro r hr
    have hp := happ b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi L r hr f hf hv
    dsimp only at hp
    let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
    have he : Real.exp (-2 * d - 2 * h - 2 * q - 2 * f) =
        Real.exp (-2 * h - 2 * f) * Real.exp (-2 * d - 2 * q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change P r ≤ sourcePairReferenceUpperConstant * ((f + 1) / (d * h)) *
      Real.exp (-2 * d - 2 * h - 2 * q - 2 * f) at hp
    rw [he] at hp
    convert hp using 1
    dsimp [a, q]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  have hb := hband P a ha hP hpoint
  convert hb using 1
  have he : Real.exp (-2 * t - 2 * h - 2 * f) =
      Real.exp (-2 * h - 2 * f) * Real.exp (-2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  dsimp [a]
  ring

end SRWTightness
