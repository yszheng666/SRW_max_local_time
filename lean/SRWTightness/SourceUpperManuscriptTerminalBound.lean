import SRWTightness.SourceUpperManuscriptTerminal

open MeasureTheory ProbabilityTheory Filter
namespace SRWTightness

/-- Restore the manuscript's nonnegative polynomial factor from the stronger envelope. -/
theorem terminal_tail_polynomial_factor (P C r d q κ : ℝ) (hP : 0 ≤ P)
    (hb : P ≤ C * r ^ 2 * Real.exp (-2 * d) / d *
      Real.exp (-2 * q - κ * (max q 0) ^ 2 / d)) :
    P ≤ C * r ^ 2 * Real.exp (-2 * d) / d * (1 + max q 0 / Real.sqrt d) *
      Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  have h0 := hP.trans hb
  have hr : 0 ≤ max q 0 / Real.sqrt d :=
    div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
  have hm := mul_nonneg h0 hr
  calc
    P ≤ C * r ^ 2 * Real.exp (-2 * d) / d *
        Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := hb
    _ ≤ (C * r ^ 2 * Real.exp (-2 * d) / d *
        Real.exp (-2 * q - κ * (max q 0) ^ 2 / d)) *
        (1 + max q 0 / Real.sqrt d) := by nlinarith only [hm]
    _ = _ := by ring

theorem source_upper_manuscript_terminal_bound (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (δ c : ℝ) (hδ : 0 < δ) (hδone : δ < 1) (hc : 0 < c) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ t : ℝ in atTop, ∀ (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * upperTerminalRadius (sourceUpperLogRadius t)) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤
        (c * upperTerminalFineRadius (sourceUpperLogRadius t)) ^ 2) →
      ∀ q : ℝ, -Real.sqrt (upperTerminalDepth (sourceUpperLogRadius t)) ≤ q →
      (gaussianGreenLaw (diskFinset (upperTerminalRadius (sourceUpperLogRadius t))) A).real
        {φ | ∃ x : A, 2 * upperTerminalDepth (sourceUpperLogRadius t) + q ≤
          φ x / Real.sqrt (2 / Real.pi)} ≤
        C * (upperTerminalFineRadius (sourceUpperLogRadius t)) ^ 2 *
          Real.exp (-2 * upperTerminalDepth (sourceUpperLogRadius t)) /
          upperTerminalDepth (sourceUpperLogRadius t) *
          (1 + max q 0 / Real.sqrt (upperTerminalDepth (sourceUpperLogRadius t))) *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / upperTerminalDepth (sourceUpperLogRadius t)) := by
  obtain ⟨C, κ, hC, hκ, ht⟩ := source_upper_manuscript_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale
      δ c hδ hδone hc
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [ht] with t ht
  intro A hA hcentral hdiam q hq
  exact terminal_tail_polynomial_factor _ C
    (upperTerminalFineRadius (sourceUpperLogRadius t))
    (upperTerminalDepth (sourceUpperLogRadius t)) q κ measureReal_nonneg
    (ht A hA hcentral hdiam q hq)

end SRWTightness
