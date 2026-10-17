import SRWTightness.SourceUpperInteriorDiskTerminal

open MeasureTheory ProbabilityTheory
namespace SRWTightness

theorem source_upper_interior_disk_green_terminal (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ C κ d₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < d₀ ∧
      ∀ (R r d q : ℝ) (A : Finset Site), 2 ≤ R → 1 ≤ r → 32 * r ≤ δ * R → A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * R) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ r ^ 2) →
      d₀ ≤ d → d = diskGreen R 0 0 / (2 / Real.pi) →
      d / 8 ≤ Real.log r → Real.log r + Real.log 64 ≤ d / 2 →
      -Real.sqrt d ≤ q →
      (gaussianGreenLaw (diskFinset R) A).real
        {φ | ∃ x : A, 2 * d + q ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
        C * r ^ 2 * Real.exp (-2 * d) / d *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  have hB : 0 ≤ diskGreenEnergyConstant / (2 / Real.pi) := by
    exact div_nonneg diskGreenEnergyConstant_pos.le (by positivity)
  obtain ⟨C, κ, d₀, hC, hκ, hd₀, ht⟩ := source_upper_interior_disk_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed
      δ (diskGreenEnergyConstant / (2 / Real.pi)) hδ hδone hB
  refine ⟨C, κ, d₀, hC, hκ, hd₀, ?_⟩
  intro R r d q A hR hr hRr hA hcentral hdiam hd hdref hhL hhU hq
  apply ht R r d q A hr hRr hA hcentral hdiam hd _ hhL hhU hq
  rw [hdref]
  exact disk_normalized_reference_log_bound R hR

end SRWTightness
