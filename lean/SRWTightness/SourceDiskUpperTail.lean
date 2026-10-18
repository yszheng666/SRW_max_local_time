import SRWTightness.SourceUpperInnerTail
import SRWTightness.SourceUpperDiskTailTransfer

open Filter MeasureTheory

namespace SRWTightness

/-- The full original-walk upper-tail proposition, with the existing external interfaces explicit. -/
theorem source_disk_upper_tail_claim (hF : TwoLevelWordFlatteningInput)
    (hinput : PotentialKernelAsymptoticInput)
    (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (hTranslation : ProjectedMarkTranslationInput)
    (hGW : GWBarrierUpperInput)
    (hTree : ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      MarkedGWTreeInput (Mark (sourceUpperBlock t b)))
    (hJoint : ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ [MeasurableSpace (List (Mark (sourceUpperBlock t b)))]
        [MeasurableSingletonClass (List (Mark (sourceUpperBlock t b)))],
        MarkedGWForestJointInput (Mark (sourceUpperBlock t b))) : DiskUpperTailClaim := by
  obtain ⟨C, hC, hinner⟩ := source_upper_inner_source_tail hF hinput hReg hBDZ hSup
    hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation hGW hTree hJoint
  exact source_upper_disk_tail_of_inner C hC hinner

end SRWTightness
