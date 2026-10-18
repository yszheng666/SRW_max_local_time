import SRWTightness.SourceUpperTerminalCountBound
import SRWTightness.ExternalProjectedMarkTranslation

open MeasureTheory ProbabilityTheory Filter
namespace SRWTightness

/-- Source terminal occupation bounds at arbitrary block centers,
including the small-count range. -/
theorem source_upper_translated_terminal_count_bound (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (hTranslation : ProjectedMarkTranslationInput)
    (δ c a : ℝ)
    (hδ : 0 < δ) (hδone : δ < 1) (hc : 0 < c) (ha : 0 < a) :
    ∃ C κ ρ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < ρ ∧ ∀ᶠ t : ℝ in atTop,
      let D := diskFinset (sourceUpperMarkRadius t)
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      ∀ (b : Site) (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * sourceUpperMarkRadius t) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ (c * r) ^ 2) →
      ∀ (K : Finset Site) (hAK : A ⊆ K) (hKD : K ⊆ D),
      K ⊆ diskFinset (a * r) →
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ k : ℕ,
      Real.sqrt (2 * (k : ℝ)) ≤ sourceUpperTarget t s + (4 + s) + d ^ (1 / 4 : ℝ) →
      let q := sourceUpperTarget t s - Real.sqrt (2 * (k : ℝ))
      (markProductLaw (translateFinset b D) (translateFinset b K) (sourceUpperIntensity t) k).real
        {Y | ∃ z : A, sourceUpperVisitCutoff t s ≤ sumMarks (translateFinset b K) k Y
          ⟨b + z, (mem_translateFinset_add b K z).2 (hAK z.property)⟩} ≤
      (if t - 1 ≤ Real.sqrt (2 * (k : ℝ)) then
        C * r ^ 2 * Real.exp (-2 * d) / d * (1 + max q 0 / Real.sqrt d) *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) else 0) +
        C * r ^ 2 * Real.exp (-ρ * t ^ 2 / d) := by
  obtain ⟨C, κ, ρ, hC, hκ, hρ, ht⟩ := source_upper_terminal_count_bound
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount
    δ c a hδ hδone hc ha
  refine ⟨C, κ, ρ, hC, hκ, hρ, ?_⟩
  filter_upwards [ht] with t ht
  dsimp only
  intro b A hA hcentral hdiam K hAK hKD hK s hs hslog k hku
  rw [hTranslation b (diskFinset (sourceUpperMarkRadius t)) A K hAK
    (sourceUpperIntensity t) k (sourceUpperVisitCutoff t s)]
  exact ht A hA hcentral hdiam K hAK hKD hK s hs hslog k hku

/-- The literal manuscript terminal occupation bound, uniformly over translated source blocks. -/
theorem source_upper_translated_terminal_occupation_bound (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (hTranslation : ProjectedMarkTranslationInput)
    (δ c a : ℝ)
    (hδ : 0 < δ) (hδone : δ < 1) (hc : 0 < c) (ha : 0 < a) :
    ∃ C κ ρ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < ρ ∧ ∀ᶠ t : ℝ in atTop,
      let D := diskFinset (sourceUpperMarkRadius t)
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      ∀ (b : Site) (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * sourceUpperMarkRadius t) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ (c * r) ^ 2) →
      ∀ (K : Finset Site) (hAK : A ⊆ K) (hKD : K ⊆ D),
      K ⊆ diskFinset (a * r) →
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ k : ℕ,
      t - 1 ≤ Real.sqrt (2 * (k : ℝ)) →
      Real.sqrt (2 * (k : ℝ)) ≤ sourceUpperTarget t s + (4 + s) + d ^ (1 / 4 : ℝ) →
      let q := sourceUpperTarget t s - Real.sqrt (2 * (k : ℝ))
      (markProductLaw (translateFinset b D) (translateFinset b K) (sourceUpperIntensity t) k).real
        {Y | ∃ z : A, sourceUpperVisitCutoff t s ≤ sumMarks (translateFinset b K) k Y
          ⟨b + z, (mem_translateFinset_add b K z).2 (hAK z.property)⟩} ≤
      C * r ^ 2 * Real.exp (-2 * d) / d * (1 + max q 0 / Real.sqrt d) *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) +
        C * r ^ 2 * Real.exp (-ρ * t ^ 2 / d) := by
  obtain ⟨C, κ, ρ, hC, hκ, hρ, ht⟩ := source_upper_translated_terminal_count_bound
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount
    hTranslation δ c a hδ hδone hc ha
  refine ⟨C, κ, ρ, hC, hκ, hρ, ?_⟩
  filter_upwards [ht] with t ht
  dsimp only
  intro b A hA hcentral hdiam K hAK hKD hK s hs hslog k hkl hku
  simpa only [if_pos hkl] using ht b A hA hcentral hdiam K hAK hKD hK s hs hslog k hku

end SRWTightness
