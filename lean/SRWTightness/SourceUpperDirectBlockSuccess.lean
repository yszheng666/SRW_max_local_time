import SRWTightness.SourceUpperBlockSuccessRadius
import SRWTightness.SourceUpperBlockDirectCount

open Filter MeasureTheory

namespace SRWTightness

/-- Source block success expressed with directly extracted buffered traversal counts. -/
def sourceUpperDirectBlockSuccess (t s : ℝ) (b : Site) : Set Sample :=
  {ω | (∃ y : sourceUpperBlock t b,
      sourceUpperVisitCutoff t s ≤ domainLocalTime (diskFinset (Real.exp t)) 0 y ω) ∧
    ∀ j : ℕ, sourceUpperBlockRoot t b < j → j ≤ sourceUpperCoarseDepth t →
      Real.sqrt (2 * ((killedChildIntervals (diskFinset (Real.exp t))
        (sourceUpperBlockInner t j b) (sourceUpperBlockOuter t j b) 0 ω).length : ℝ)) ≤
          sourceUpperBarrier t s j}

/-- Direct-traversal and forest-count block successes have equal actual probabilities. -/
theorem source_upper_direct_block_success_probability (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t, ∀ s : ℝ,
      pathLaw.real (sourceUpperDirectBlockSuccess t s b) =
        pathLaw.real (sourceUpperBlockSuccess t s b) := by
  filter_upwards [source_upper_block_count_eq_direct_ae hF] with t ht
  intro b hb s
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ht b hb] with ω hω
  apply propext
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro _
  constructor
  · intro h j hj hJ
    rw [hω j hj.le hJ]
    exact h j hj hJ
  · intro h j hj hJ
    rw [← hω j hj.le hJ]
    exact h j hj hJ

/-- Source (4.34) for direct buffered traversals in the original radius parameter. -/
theorem source_upper_direct_block_success_limsup_radius (hF : TwoLevelWordFlatteningInput)
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
    ∃ H : ℝ, 0 < H ∧ ∀ s : ℝ, 0 ≤ s →
      limsup (fun R : ℝ ↦ ∑ b ∈ sourceUpperBlockCenters (Real.log R),
        pathLaw.real (sourceUpperDirectBlockSuccess (Real.log R) s b)) atTop ≤
          H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) := by
  obtain ⟨H, hH, ht⟩ := source_upper_block_success_limsup_radius hinput hReg hBDZ hSup
    hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation hGW hTree hJoint
  refine ⟨H, hH, ?_⟩
  intro s hs
  have heq : (fun R : ℝ ↦ ∑ b ∈ sourceUpperBlockCenters (Real.log R),
      pathLaw.real (sourceUpperDirectBlockSuccess (Real.log R) s b)) =ᶠ[atTop]
      (fun R : ℝ ↦ ∑ b ∈ sourceUpperBlockCenters (Real.log R),
        pathLaw.real (sourceUpperBlockSuccess (Real.log R) s b)) := by
    filter_upwards [Real.tendsto_log_atTop.eventually
      (source_upper_direct_block_success_probability hF)] with R hr
    exact Finset.sum_congr rfl (fun b hb ↦ hr b hb s)
  rw [limsup_congr heq]
  exact ht s hs

end SRWTightness
