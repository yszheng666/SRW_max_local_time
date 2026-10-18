import SRWTightness.SourceUpperTranslatedTerminalCount
import SRWTightness.SourceUpperTerminalBlockGeometry
import SRWTightness.SourceUpperForestJointProbability
import SRWTightness.MarkListProductProbability

open Filter MeasureTheory

namespace SRWTightness

/-- The terminal occupation estimate holds for every actual upper-block mark list. -/
theorem source_upper_block_mark_list_bound (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (hTranslation : ProjectedMarkTranslationInput) :
    ∃ C κ ρ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < ρ ∧ ∀ᶠ t : ℝ in atTop,
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      ∀ b : Site, ∀ [MeasurableSpace (List (Mark (sourceUpperBlock t b)))]
        [MeasurableSingletonClass (List (Mark (sourceUpperBlock t b)))],
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ k : ℕ,
      Real.sqrt (2 * (k : ℝ)) ≤ sourceUpperTarget t s + (4 + s) + d ^ (1 / 4 : ℝ) →
      let q := sourceUpperTarget t s - Real.sqrt (2 * (k : ℝ))
      (independentForestLaw (sourceUpperBlockMarkLaw t b) k).real
        (sourceUpperMarkListHighEvent t s b) ≤
      (if t - 1 ≤ Real.sqrt (2 * (k : ℝ)) then
        C * r ^ 2 * Real.exp (-2 * d) / d * (1 + max q 0 / Real.sqrt d) *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) else 0) +
        C * r ^ 2 * Real.exp (-ρ * t ^ 2 / d) := by
  obtain ⟨C, κ, ρ, hC, hκ, hρ, hh⟩ := source_upper_translated_terminal_count_bound
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount
    hTranslation (1 / 2) 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, κ, ρ, hC, hκ, hρ, ?_⟩
  filter_upwards [hh, source_upper_terminal_block_geometry] with t ht hg
  dsimp only at ht ⊢
  intro b inst₁ inst₂ s hs hslog k hku
  have hp := ht b (sourceUpperBlock t 0) (sourceUpperBlock_nonempty t) hg.1 hg.2.1
    (sourceUpperBlock t 0) (Finset.Subset.refl _) hg.2.2.1 hg.2.2.2 s hs hslog k hku
  rw [mark_product_translated_full_event, sourceUpperBlock_translate] at hp
  have he := congrArg ENNReal.toReal (mark_list_product_probability
    (translateFinset b (diskFinset (sourceUpperMarkRadius t))) (sourceUpperBlock t b)
    (sourceUpperIntensity t) k (sourceUpperVisitCutoff t s))
  exact he.le.trans hp

end SRWTightness
