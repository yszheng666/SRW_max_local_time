import SRWTightness.SourceUpperSupportedWindowProbability
import SRWTightness.SourceUpperTerminalIntegralBound

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The finite principal contribution retaining both true window support and branching cutoff. -/
noncomputable def sourceUpperSupportedPrincipalSum (t s C κ B : ℝ) (b : Site) (J : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (⌊2 * t + 1⌋₊ + 1),
    ENNReal.ofReal (sourceUpperTerminalWindowWeight t s C κ (t - 1 + i)) *
      if -(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤
        sourceUpperTarget t s - (t - 1 + i) ∧ t - 1 + i ≤ sourceUpperBranchingEnd t s then
        ENNReal.ofReal (sourceUpperBranchingWindowFactor t s B (sourceUpperBlockRoot t b)
          J (t - 1 + i)) else 0

/-- The main terminal integral obeys the supported finite branching-window sum. -/
theorem source_upper_supported_principal_sum (hScale : ExponentialFloorScaleInput)
    (hGW : GWBarrierUpperInput) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ J : ℕ, 0 < J → (J : ℝ) ≤ t ^ 2 →
      ∀ C κ : ℝ, 0 ≤ C → 0 ≤ κ →
      (∫⁻ g in sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b),
        sourceUpperTerminalIntegrand t s C κ (sourceUpperBlockForestDepth t b) g
        ∂geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)) ≤
          sourceUpperSupportedPrincipalSum t s C κ B b J := by
  obtain ⟨B, hB, hp⟩ := source_upper_supported_window_probability hScale hGW
  refine ⟨B, hB, ?_⟩
  filter_upwards [source_upper_terminal_weighted_windows hScale, hp] with t ht hbnd
  intro b hb s hs hslog J hJ hJcap C κ hC hκ
  apply (ht b hb s hs hslog J C κ hC hκ).trans
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_left' (hbnd b hb s hs hslog J hJ hJcap (t - 1 + i)
    (by linarith [Nat.cast_nonneg (α := ℝ) i])) _

/-- Actual terminal mark probabilities integrate to the supported principal sum and one error. -/
theorem source_upper_supported_principal_bound (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (hTranslation : ProjectedMarkTranslationInput)
    (hGW : GWBarrierUpperInput) :
    ∃ C κ ρ B : ℝ, 0 < C ∧ 0 < κ ∧ 0 < ρ ∧ 0 < B ∧ ∀ᶠ t : ℝ in atTop,
      ∀ b ∈ sourceUpperBlockCenters t,
      ∀ [MeasurableSpace (List (Mark (sourceUpperBlock t b)))]
        [MeasurableSingletonClass (List (Mark (sourceUpperBlock t b)))],
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ J : ℕ, 0 < J → (J : ℝ) ≤ t ^ 2 →
        (∫⁻ g in sourceUpperGWBand t s (sourceUpperBlockRoot t b)
            (sourceUpperBlockForestDepth t b),
          independentForestLaw (sourceUpperBlockMarkLaw t b)
            (geometricGWPopulation g (sourceUpperBlockForestDepth t b))
            (sourceUpperMarkListHighEvent t s b)
          ∂geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)) ≤
        sourceUpperSupportedPrincipalSum t s C κ B b J +
          ENNReal.ofReal (sourceUpperTerminalRemainder t C ρ) := by
  obtain ⟨C, κ, ρ, hC, hκ, hρ, hi⟩ := source_upper_terminal_integral_bound
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount hTranslation
  obtain ⟨B, hB, hp⟩ := source_upper_supported_principal_sum hScale hGW
  refine ⟨C, κ, ρ, B, hC, hκ, hρ, hB, ?_⟩
  filter_upwards [hi, hp] with t ht hbnd
  intro b hb inst₁ inst₂ s hs hslog J hJ hJcap
  exact (ht b hb s hs hslog J).trans
    (add_le_add (hbnd b hb s hs hslog J hJ hJcap C κ hC.le hκ.le) le_rfl)

end SRWTightness
