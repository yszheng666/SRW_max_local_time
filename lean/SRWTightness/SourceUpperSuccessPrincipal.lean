import SRWTightness.SourceUpperSuccessProbability
import SRWTightness.SourceUpperForestJointProbability
import SRWTightness.SourceUpperSupportedPrincipalSum

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Actual positive-root success is bounded by the supported principal kernel and terminal error. -/
theorem source_upper_success_principal (hinput : PotentialKernelAsymptoticInput)
    (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (hTranslation : ProjectedMarkTranslationInput)
    (hGW : GWBarrierUpperInput) :
    ∃ A W K C κ ρ B : ℝ, 0 ≤ A ∧ 0 ≤ W ∧ 1 ≤ K ∧
      0 < C ∧ 0 < κ ∧ 0 < ρ ∧ 0 < B ∧ ∀ᶠ t : ℝ in atTop,
      ∀ b ∈ sourceUpperBlockCenters t, MarkedGWTreeInput (Mark (sourceUpperBlock t b)) →
      ∀ [MeasurableSpace (List (Mark (sourceUpperBlock t b)))]
        [MeasurableSingletonClass (List (Mark (sourceUpperBlock t b)))],
      MarkedGWForestJointInput (Mark (sourceUpperBlock t b)) →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
        (sourceUpperBlockForestDepth t b))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b)))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b)))],
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ J : ℕ, 0 < J → (J : ℝ) ≤ t ^ 2 →
      pathLaw {ω | sourceUpperBlockRootCount t b ω = J ∧
        ω ∈ sourceUpperBlockSuccess t s b} ≤
        ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1) *
          Real.exp ((3584 * A + 96 * W) * t ^ 2 * sourceUpperLogRadius t *
            Real.exp (-3 * sourceUpperLogRadius t / 4))) *
          (sourceUpperSupportedPrincipalSum t s C κ B b J +
            ENNReal.ofReal (sourceUpperTerminalRemainder t C ρ)) := by
  obtain ⟨A, W, K, hA, hW, hK, ha⟩ := source_upper_success_probability hinput hScale
  obtain ⟨C, κ, ρ, B, hC, hκ, hρ, hB, hp⟩ := source_upper_supported_principal_bound
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount
    hTranslation hGW
  refine ⟨A, W, K, C, κ, ρ, B, hA, hW, hK, hC, hκ, hρ, hB, ?_⟩
  filter_upwards [ha, hp, source_upper_forest_joint_probability] with t ha hp hj
  intro b hb htree inst₁ inst₂ hjoint inst₃ inst₄ inst₅ inst₆ s hs hslog J hJ hJcap
  apply (ha b hb htree s hs hslog J hJ hJcap).trans
  apply mul_le_mul_left'
  have hm : independentForestLaw
      (finiteRecordReferenceMeasure (sourceUpperBlockMarkLaw t b)
        (sourceUpperBlockForestDepth t b)) J
      {rs | rs.length = J ∧ rs ∈ sourceUpperForestSuccess t s b} ≤
      independentForestLaw
        (finiteRecordReferenceMeasure (sourceUpperBlockMarkLaw t b)
          (sourceUpperBlockForestDepth t b)) J (sourceUpperForestSuccess t s b) :=
    measure_mono (fun _ h ↦ h.2)
  rw [hj b hb hjoint s J] at hm
  exact hm.trans (hp b hb s hs hslog J hJ hJcap)

end SRWTightness
