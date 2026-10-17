import SRWTightness.SourceUpperInnerSourceBound

open Filter MeasureTheory

namespace SRWTightness

/-- For fixed nonnegative excess height the source square-root inner event has the two expected limiting tails. -/
theorem source_upper_inner_source_tail (hF : TwoLevelWordFlatteningInput)
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
        {ω | ∃ x ∈ diskFinset (R / 2), diskCenter R + s ≤
          Real.sqrt (localTime ω (exitSteps R ω) x : ℝ)}) atTop ≤
        C * ((1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) +
          Real.exp (-3 * s / 2)) := by
  obtain ⟨U, H, hU, hH, ht⟩ := source_upper_inner_source_limsup hF hinput hReg
    hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation
    hGW hTree hJoint
  refine ⟨U + H, by linarith, ?_⟩
  intro s hs
  apply (ht s hs).trans
  have hp : 0 ≤ (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) := by positivity
  have hq : 0 ≤ Real.exp (-3 * s / 2) := (Real.exp_pos _).le
  nlinarith [mul_nonneg hU.le hp, mul_nonneg hH.le hq]

end SRWTightness
