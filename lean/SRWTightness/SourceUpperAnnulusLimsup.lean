import SRWTightness.SourceUpperAnnulusExplicitBound
import SRWTightness.SourceUpperRootCapLimit

open Filter MeasureTheory
open scoped Topology

namespace SRWTightness

/-- For fixed nonnegative excess height the actual annulus has the two expected limiting tails. -/
theorem source_upper_annulus_limsup (hF : TwoLevelWordFlatteningInput)
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
      limsup (fun t : ℝ ↦ pathLaw.real (sourceUpperAnnulusHighEvent t s)) atTop ≤
        U * Real.exp (-3 * s / 2) +
          H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) := by
  obtain ⟨U, H, E, hU, hH, hE, ht⟩ := source_upper_annulus_explicit_bound hF hinput hReg
    hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation hGW
  refine ⟨U, H, hU, hH, ?_⟩
  intro s hs
  have he : Tendsto (fun t : ℝ ↦ E * Real.exp (-2 * t)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa only [Function.comp_apply, id_eq, neg_mul, mul_zero] using hh.const_mul E
  let L := U * Real.exp (-3 * s / 2) +
    H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s))
  have hlim : Tendsto (fun t : ℝ ↦
      (U * Real.exp (-3 * s / 2) + 25 * Real.exp (2 * t - t ^ 2 / (4 * Real.log t))) +
      (H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) + E * Real.exp (-2 * t)))
      atTop (𝓝 L) := by
    have hfirst := (tendsto_const_nhds
      (x := U * Real.exp (-3 * s / 2))).add source_upper_root_cap_majorant_vanishes
    have hsecond := (tendsto_const_nhds
      (x := H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)))).add he
    simpa [L] using hfirst.add hsecond
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun t ↦ measureReal_nonneg))
  filter_upwards [ht, hTree, hJoint,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop s),
    (tendsto_order.1 hlim).2 (L + ε) (by linarith)] with t ht htree hjoint hslog hbound
  exact (ht htree hjoint s hs hslog).trans hbound.le

end SRWTightness
