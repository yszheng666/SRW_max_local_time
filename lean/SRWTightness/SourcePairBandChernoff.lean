import SRWTightness.SourcePairMarkChernoff
import SRWTightness.SourceGWWeightedBandUpper

open MeasureTheory ProbabilityTheory Filter

namespace SRWTightness

/-- Integrating the actual pair reference probabilities over the full coarse deficit band. -/
theorem source_pair_reference_band_chernoff
    (hUpper : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (A : ℝ)
      (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (f : ℝ),
    let d := sourceLowerTime (sourceLowerRadius t)
    let h := d - sourceObservationTime t A I (I - i + 1)
    let L := (sourceCoarseGeneration t).toNat
    (∫ r in sourceGWCoarseBandEvent t L,
      sourcePairMarkProbability t A b I i z y (geometricGWPopulation r L) f
        ∂geometricGWRecordLaw 1 L) ≤
      C * d * Real.exp (-2 * t - 2 * h - 2 * f) := by
  obtain ⟨G, hG, hband⟩ := source_gw_weighted_band_upper hUpper
  refine ⟨G * sourcePairChernoffConstant, by
    exact mul_pos hG sourcePairChernoffConstant_pos, ?_⟩
  filter_upwards [hband, source_pair_mark_probability_chernoff,
    eventually_ge_atTop (sourceScaleThreshold 4)] with t hband happ ht4
  intro b A hA ht I hI i hi z y hz hρ hlo hhi f
  dsimp only
  let d := sourceLowerTime (sourceLowerRadius t)
  let h := d - sourceObservationTime t A I (I - i + 1)
  let L := (sourceCoarseGeneration t).toNat
  let P := fun r ↦ sourcePairMarkProbability t A b I i z y (geometricGWPopulation r L) f
  let a := sourcePairChernoffConstant * d * Real.exp (-2 * h - 2 * f)
  have hd : 0 < d := by
    have hd1 := sourceLowerTime_ge_one t ht4
    dsimp [d]
    linarith
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (mul_nonneg sourcePairChernoffConstant_pos.le hd.le) (Real.exp_nonneg _)
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
    have hp := happ b A hA ht I hI i hi z y hz hρ hlo hhi L r hr f
    dsimp only at hp
    let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
    have he : Real.exp (-2 * d - 2 * h - 2 * q - 2 * f) =
        Real.exp (-2 * h - 2 * f) * Real.exp (-2 * d - 2 * q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change P r ≤ sourcePairChernoffConstant *
      Real.exp (-2 * d - 2 * h - 2 * q - 2 * f) at hp
    rw [he] at hp
    convert hp using 1
    dsimp [a, q]
    field_simp [ne_of_gt hd]
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
