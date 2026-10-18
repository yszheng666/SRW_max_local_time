import SRWTightness.SourceUpperTerminalIntegrandBound

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The terminal error integrates to one uniform remainder under the branching probability law. -/
theorem source_upper_terminal_integral_bound (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (hTranslation : ProjectedMarkTranslationInput) :
    ∃ C κ ρ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < ρ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ b ∈ sourceUpperBlockCenters t,
      ∀ [MeasurableSpace (List (Mark (sourceUpperBlock t b)))]
        [MeasurableSingletonClass (List (Mark (sourceUpperBlock t b)))],
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ J : ℕ,
        (∫⁻ g in sourceUpperGWBand t s (sourceUpperBlockRoot t b)
            (sourceUpperBlockForestDepth t b),
          independentForestLaw (sourceUpperBlockMarkLaw t b)
            (geometricGWPopulation g (sourceUpperBlockForestDepth t b))
            (sourceUpperMarkListHighEvent t s b)
          ∂geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)) ≤
        (∫⁻ g in sourceUpperGWBand t s (sourceUpperBlockRoot t b)
            (sourceUpperBlockForestDepth t b),
          sourceUpperTerminalIntegrand t s C κ (sourceUpperBlockForestDepth t b) g
          ∂geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)) +
            ENNReal.ofReal (sourceUpperTerminalRemainder t C ρ) := by
  obtain ⟨C, κ, ρ, hC, hκ, hρ, hh⟩ := source_upper_terminal_integrand_bound
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation
  refine ⟨C, κ, ρ, hC, hκ, hρ, ?_⟩
  filter_upwards [hh] with t ht
  intro b hb inst₁ inst₂ s hs hslog J
  apply (setLIntegral_mono (measurable_of_countable _) (ht b hb s hs hslog)).trans
  rw [lintegral_add_left (measurable_of_countable _), lintegral_const,
    Measure.restrict_apply_univ]
  apply add_le_add le_rfl
  calc
    _ ≤ ENNReal.ofReal (sourceUpperTerminalRemainder t C ρ) * 1 :=
      mul_le_mul_left' (show geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)
        (sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b)) ≤ 1
        from (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)) _
    _ = _ := mul_one _

end SRWTightness
