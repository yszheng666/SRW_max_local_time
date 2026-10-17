import SRWTightness.SourceUpperCappedSuccessTotal
import SRWTightness.SourceUpperBlockRootReduction
import SRWTightness.SourceUpperBlockCapSum

open Filter MeasureTheory

namespace SRWTightness

/-- The untruncated sum of actual block successes has the desired tail and two vanishing errors. -/
theorem source_upper_block_success_total (hinput : PotentialKernelAsymptoticInput)
    (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (hTranslation : ProjectedMarkTranslationInput)
    (hGW : GWBarrierUpperInput) :
    ∃ H E : ℝ, 0 < H ∧ 0 < E ∧ ∀ᶠ t : ℝ in atTop,
      (∀ b ∈ sourceUpperBlockCenters t, MarkedGWTreeInput (Mark (sourceUpperBlock t b))) →
      (∀ b ∈ sourceUpperBlockCenters t,
        ∀ [MeasurableSpace (List (Mark (sourceUpperBlock t b)))]
          [MeasurableSingletonClass (List (Mark (sourceUpperBlock t b)))],
          MarkedGWForestJointInput (Mark (sourceUpperBlock t b))) →
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      (∑ b ∈ sourceUpperBlockCenters t, pathLaw.real (sourceUpperBlockSuccess t s b)) ≤
        25 * Real.exp (2 * t - t ^ 2 / (4 * Real.log t)) +
          (H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) + E * Real.exp (-2 * t)) := by
  obtain ⟨H, E, hH, hE, hp⟩ := source_upper_capped_success_total hinput hReg hBDZ hSup
    hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation hGW
  refine ⟨H, E, hH, hE, ?_⟩
  filter_upwards [hp, source_upper_block_root_probability_sum,
    source_upper_block_cap_sum_ennreal hinput] with t hp hr hc
  intro htree hjoint s hs hslog
  have hh := (hr s hs hslog).trans (add_le_add hc (hp htree hjoint s hs hslog))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hh
  have heq : (∑ b ∈ sourceUpperBlockCenters t, pathLaw (sourceUpperBlockSuccess t s b)) =
      ENNReal.ofReal (∑ b ∈ sourceUpperBlockCenters t,
        pathLaw.real (sourceUpperBlockSuccess t s b)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun b _ ↦ measureReal_nonneg)]
    apply Finset.sum_congr rfl
    intro b hb
    exact (ofReal_measureReal (measure_ne_top _ _)).symm
  rw [heq] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

end SRWTightness
