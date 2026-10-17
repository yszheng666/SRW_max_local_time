import SRWTightness.SourceUpperAnnulusPrincipalBound
import SRWTightness.SourceUpperCrossingProbability

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The actual annulus has an explicit real probability bound, including both exceptional costs. -/
theorem source_upper_annulus_explicit_bound (hF : TwoLevelWordFlatteningInput)
    (hinput : PotentialKernelAsymptoticInput)
    (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (hTranslation : ProjectedMarkTranslationInput)
    (hGW : GWBarrierUpperInput) :
    ∃ U H E : ℝ, 0 < U ∧ 0 < H ∧ 0 < E ∧ ∀ᶠ t : ℝ in atTop,
      (∀ b ∈ sourceUpperBlockCenters t, MarkedGWTreeInput (Mark (sourceUpperBlock t b))) →
      (∀ b ∈ sourceUpperBlockCenters t,
        ∀ [MeasurableSpace (List (Mark (sourceUpperBlock t b)))]
          [MeasurableSingletonClass (List (Mark (sourceUpperBlock t b)))],
          MarkedGWForestJointInput (Mark (sourceUpperBlock t b))) →
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      pathLaw.real (sourceUpperAnnulusHighEvent t s) ≤
        (U * Real.exp (-3 * s / 2) +
          25 * Real.exp (2 * t - t ^ 2 / (4 * Real.log t))) +
        (H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) + E * Real.exp (-2 * t)) := by
  obtain ⟨H, E, hH, hE, hp⟩ := source_upper_annulus_principal_bound hF hinput hReg hBDZ
    hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation hGW
  obtain ⟨U, hU, hu⟩ := source_upper_crossing_probability hinput hScale
  refine ⟨U, H, E, hU, hH, hE, ?_⟩
  filter_upwards [hp, hu, source_upper_root_cap_probability hinput] with t hp hu hc
  intro htree hjoint s hs hslog
  have hcross : pathLaw (sourceUpperCrossingEvent t s) ≤
      ENNReal.ofReal (U * Real.exp (-3 * s / 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hu s hs hslog)
  have hcap : pathLaw (sourceUpperRootCapEvent t) ≤
      ENNReal.ofReal (25 * Real.exp (2 * t - t ^ 2 / (4 * Real.log t))) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hc
  have hh := (hp htree hjoint s hs hslog).trans
    (add_le_add (add_le_add hcross hcap) le_rfl)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hh
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  exact hr

end SRWTightness
