import SRWTightness.SourceUpperInnerRadius
import SRWTightness.SourceUpperInnerSourceEvent

open Filter MeasureTheory

namespace SRWTightness

/-- For fixed nonnegative excess height the source square-root inner event has the two expected limiting tails. -/
theorem source_upper_inner_source_limsup (hF : TwoLevelWordFlatteningInput)
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
    ∃ U H : ℝ, 0 < U ∧ 0 < H ∧ ∀ s : ℝ, 0 ≤ s →
      limsup (fun R : ℝ ↦ pathLaw.real
        {ω | ∃ x ∈ diskFinset (R / 2), diskCenter R + s ≤
          Real.sqrt (localTime ω (exitSteps R ω) x : ℝ)}) atTop ≤
        U * Real.exp (-3 * s / 2) +
          H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) := by
  obtain ⟨U, H, hU, hH, ht⟩ := source_upper_inner_limsup_radius hF hinput hReg
    hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation
    hGW hTree hJoint
  refine ⟨U, H, hU, hH, ?_⟩
  intro s hs
  have heq : (fun R : ℝ ↦ pathLaw.real (sourceUpperInnerHighEvent (Real.log R) s)) =ᶠ[atTop]
      (fun R : ℝ ↦ pathLaw.real
        {ω | ∃ x ∈ diskFinset (R / 2), diskCenter R + s ≤
          Real.sqrt (localTime ω (exitSteps R ω) x : ℝ)}) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 2)] with R hR hlog
    rw [source_upper_inner_event_at_radius R s hR hlog hs]
  rw [← limsup_congr heq]
  exact ht s hs

end SRWTightness
