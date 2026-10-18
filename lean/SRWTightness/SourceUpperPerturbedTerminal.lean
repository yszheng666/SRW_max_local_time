import SRWTightness.SourceUpperManuscriptTerminal
import SRWTightness.SourceUpperTerminalHeightPerturbation

open MeasureTheory ProbabilityTheory Filter
namespace SRWTightness

theorem source_upper_perturbed_terminal (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (δ c E : ℝ) (hδ : 0 < δ) (hδone : δ < 1) (hc : 0 < c) (hE : 0 ≤ E) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ t : ℝ in atTop, ∀ (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * upperTerminalRadius (sourceUpperLogRadius t)) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤
        (c * upperTerminalFineRadius (sourceUpperLogRadius t)) ^ 2) →
      ∀ q ε : ℝ, -E ≤ ε →
      -Real.sqrt (upperTerminalDepth (sourceUpperLogRadius t)) ≤ q + ε →
      (gaussianGreenLaw (diskFinset (upperTerminalRadius (sourceUpperLogRadius t))) A).real
        {φ | ∃ x : A, 2 * upperTerminalDepth (sourceUpperLogRadius t) + (q + ε) ≤
          φ x / Real.sqrt (2 / Real.pi)} ≤
        C * (upperTerminalFineRadius (sourceUpperLogRadius t)) ^ 2 *
          Real.exp (-2 * upperTerminalDepth (sourceUpperLogRadius t)) /
          upperTerminalDepth (sourceUpperLogRadius t) *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / upperTerminalDepth (sourceUpperLogRadius t)) := by
  obtain ⟨C, κ, hC, hκ, ht⟩ := source_upper_manuscript_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale
      δ c hδ hδone hc
  obtain ⟨u₀, hu₀, hs⟩ := source_upper_terminal_scale_conditions hScale c 1 hc (by norm_num)
  refine ⟨C * Real.exp (2 * E + κ * E ^ 2), κ / 2, by positivity, by positivity, ?_⟩
  filter_upwards [ht, sourceUpperLogRadius_eventually u₀] with t ht hu
  intro A hA hcentral hdiam q ε hε hq
  have hd : 1 ≤ upperTerminalDepth (sourceUpperLogRadius t) :=
    (hs (sourceUpperLogRadius t) hu).2.2.2.1
  have hd0 : 0 < upperTerminalDepth (sourceUpperLogRadius t) := by linarith
  have hb := ht A hA hcentral hdiam (q + ε) hq
  have he := source_upper_terminal_height_perturbation q ε E κ
    (upperTerminalDepth (sourceUpperLogRadius t)) hE hκ hd hε
  have hm := mul_le_mul_of_nonneg_left he
    (show 0 ≤ C * (upperTerminalFineRadius (sourceUpperLogRadius t)) ^ 2 *
      Real.exp (-2 * upperTerminalDepth (sourceUpperLogRadius t)) /
      upperTerminalDepth (sourceUpperLogRadius t) by positivity)
  exact hb.trans (by convert hm using 1 <;> ring)

end SRWTightness
