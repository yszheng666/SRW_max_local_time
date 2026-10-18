import SRWTightness.SourceUpperInnerTail
import SRWTightness.SourceUpperClosedTailTransfer

open Filter MeasureTheory

namespace SRWTightness

/-- Source (4.37) for the literal closed half-radius region, with existing interfaces explicit. -/
theorem source_upper_closed_inner_tail (hF : TwoLevelWordFlatteningInput)
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
        MarkedGWForestJointInput (Mark (sourceUpperBlock t b))) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s →
      limsup (fun R : ℝ ↦ pathLaw.real
        {ω | ∃ x : Site, Real.sqrt (normSq x) ≤ R / 2 ∧
          diskCenter R + s ≤ Real.sqrt (localTime ω (exitSteps R ω) x : ℝ)}) atTop ≤
        C * ((1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) + Real.exp (-3 * s / 2)) := by
  obtain ⟨C, hC, hinner⟩ := source_upper_inner_source_tail hF hinput hReg hBDZ hSup
    hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation hGW hTree hJoint
  simpa only [sourceUpperClosedInnerEvent] using source_upper_closed_tail_of_inner C hC hinner

end SRWTightness
