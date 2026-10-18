import SRWTightness.SourceUpperBlockSuccessLimsup
import SRWTightness.SourceUpperRootCapLimit

open Filter MeasureTheory
open scoped Topology

namespace SRWTightness

/-- Source (4.34) in the original outer-radius parameter, with actual untruncated block successes. -/
theorem source_upper_block_success_limsup_radius (hinput : PotentialKernelAsymptoticInput)
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
        pathLaw.real (sourceUpperBlockSuccess (Real.log R) s b)) atTop ≤
          H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) := by
  obtain ⟨H, E, hH, hE, ht⟩ := source_upper_block_success_total hinput hReg hBDZ hSup
    hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation hGW
  refine ⟨H, hH, ?_⟩
  intro s hs
  have he : Tendsto (fun t : ℝ ↦ E * Real.exp (-2 * t)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa only [Function.comp_apply, id_eq, neg_mul, mul_zero] using hh.const_mul E
  let L := H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s))
  have hlim : Tendsto (fun t : ℝ ↦
      25 * Real.exp (2 * t - t ^ 2 / (4 * Real.log t)) + (L + E * Real.exp (-2 * t)))
      atTop (𝓝 L) := by
    simpa using source_upper_root_cap_majorant_vanishes.add
      ((tendsto_const_nhds (x := L)).add he)
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop
    (fun t ↦ Finset.sum_nonneg (fun b _ ↦ measureReal_nonneg)))
  filter_upwards [Real.tendsto_log_atTop.eventually ht,
    Real.tendsto_log_atTop.eventually hTree, Real.tendsto_log_atTop.eventually hJoint,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop s),
    (tendsto_order.1 (hlim.comp Real.tendsto_log_atTop)).2 (L + ε) (by linarith)]
    with R ht htree hjoint hslog hbound
  exact (ht htree hjoint s hs hslog).trans hbound.le

end SRWTightness
