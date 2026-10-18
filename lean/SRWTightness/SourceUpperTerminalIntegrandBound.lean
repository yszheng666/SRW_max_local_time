import SRWTightness.SourceUpperTerminalIntegrand

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The actual terminal mark probability is bounded pointwise throughout the full GW band. -/
theorem source_upper_terminal_integrand_bound (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (hTranslation : ProjectedMarkTranslationInput) :
    ∃ C κ ρ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < ρ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ b ∈ sourceUpperBlockCenters t,
      ∀ [MeasurableSpace (List (Mark (sourceUpperBlock t b)))]
        [MeasurableSingletonClass (List (Mark (sourceUpperBlock t b)))],
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ g ∈ sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b),
        independentForestLaw (sourceUpperBlockMarkLaw t b)
          (geometricGWPopulation g (sourceUpperBlockForestDepth t b))
          (sourceUpperMarkListHighEvent t s b) ≤
        sourceUpperTerminalIntegrand t s C κ (sourceUpperBlockForestDepth t b) g +
          ENNReal.ofReal (sourceUpperTerminalRemainder t C ρ) := by
  obtain ⟨C, κ, ρ, hC, hκ, hρ, hh⟩ := source_upper_block_mark_list_bound
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation
  refine ⟨C, κ, ρ, hC, hκ, hρ, ?_⟩
  filter_upwards [hh, source_upper_branching_depth_bounds,
    source_upper_barrier_terminal hScale, source_upper_block_mark_probability]
    with t ht hd he hp
  intro b hb inst₁ inst₂ s hs hslog g hg
  letI := hp b
  have hn := sourceUpperBlockForestDepth_eq_remaining t b
  have hk := (hd b hb).1
  have hnpos : 0 < sourceUpperBlockForestDepth t b := by omega
  have hsum : sourceUpperBlockRoot t b + sourceUpperBlockForestDepth t b =
      sourceUpperCoarseDepth t := by omega
  have hbar := hg (sourceUpperBlockForestDepth t b) hnpos le_rfl
  rw [hsum, he s] at hbar
  have hbound := ht b s hs hslog (geometricGWPopulation g (sourceUpperBlockForestDepth t b)) hbar
  have hbnd : (independentForestLaw (sourceUpperBlockMarkLaw t b)
      (geometricGWPopulation g (sourceUpperBlockForestDepth t b))).real
      (sourceUpperMarkListHighEvent t s b) ≤
      (if t - 1 ≤ geometricGWHeight g (sourceUpperBlockForestDepth t b) then
        sourceUpperTerminalMain t s C κ (geometricGWHeight g (sourceUpperBlockForestDepth t b))
        else 0) + sourceUpperTerminalRemainder t C ρ := hbound
  calc
    _ = ENNReal.ofReal ((independentForestLaw (sourceUpperBlockMarkLaw t b)
        (geometricGWPopulation g (sourceUpperBlockForestDepth t b))).real
        (sourceUpperMarkListHighEvent t s b)) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := (ENNReal.ofReal_le_ofReal hbnd).trans (by
      simpa only [sourceUpperTerminalIntegrand, apply_ite, ENNReal.ofReal_zero] using
        (ENNReal.ofReal_add_le (p := if t - 1 ≤ geometricGWHeight g
          (sourceUpperBlockForestDepth t b) then sourceUpperTerminalMain t s C κ
            (geometricGWHeight g (sourceUpperBlockForestDepth t b)) else 0)
          (q := sourceUpperTerminalRemainder t C ρ)))

end SRWTightness
