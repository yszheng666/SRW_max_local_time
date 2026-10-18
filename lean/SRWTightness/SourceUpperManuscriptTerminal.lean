import SRWTightness.SourceUpperInteriorExactTerminal
import SRWTightness.SourceUpperLogRadius

open MeasureTheory ProbabilityTheory Filter
namespace SRWTightness

theorem source_upper_manuscript_terminal (hReg : FiniteGaussianRegressionInput)
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
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / upperTerminalDepth (sourceUpperLogRadius t)) := by
  obtain ⟨C, κ, u₀, hC, hκ, hu₀, ht⟩ := source_upper_interior_exact_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale
      δ c hδ hδone hc
  refine ⟨C, κ, hC, hκ, ?_⟩
  exact (sourceUpperLogRadius_eventually u₀).mono (fun t hu ↦ ht (sourceUpperLogRadius t) hu)

end SRWTightness
