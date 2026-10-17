import SRWTightness.SourceUpperCappedSuccessTotal

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The actual annulus probability has the principal tail, vanishing error and two explicit exceptions. -/
theorem source_upper_annulus_principal_bound (hF : TwoLevelWordFlatteningInput)
    (hinput : PotentialKernelAsymptoticInput)
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
      pathLaw (sourceUpperAnnulusHighEvent t s) ≤
        pathLaw (sourceUpperCrossingEvent t s) + pathLaw (sourceUpperRootCapEvent t) +
          ENNReal.ofReal (H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) +
            E * Real.exp (-2 * t)) := by
  obtain ⟨H, E, hH, hE, ht⟩ := source_upper_capped_success_total hinput hReg hBDZ hSup
    hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation hGW
  refine ⟨H, E, hH, hE, ?_⟩
  filter_upwards [ht, source_upper_annulus_root_probability hF] with t ht hr
  intro htree hjoint s hs hslog
  exact (hr s hs hslog).trans (add_le_add le_rfl (ht htree hjoint s hs hslog))

end SRWTightness
