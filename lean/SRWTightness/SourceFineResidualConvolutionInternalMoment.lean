import SRWTightness.SubGaussianPositiveMomentInternal
import SRWTightness.SourceFineResidualSumTail
import SRWTightness.SourceUpperConvolutionProbability

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- Conditioning the actual fine/residual sum gives the full literal integral in source(4.8). -/
theorem source_fine_residual_gaussian_convolution_internal_moment (hBDZ :
    BDZDyadicSquareMaximumInput)
    (hConv : GaussianPositiveConvolutionInput)
    (hSup : PlanarGaussianIncrementSupInput)
    (hGreen : BufferedSquareGreenInput) (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ C c h₀ B : ℝ, 0 < C ∧ 0 < c ∧ 0 < h₀ ∧ 0 ≤ B ∧
      ∀ (D E : Finset Site) (a b : Site) (m n : ℕ),
        D = latticeSquareInterior b (2 ^ m) → E = latticeSquareInterior a (2 ^ n) →
        2 ≤ n → n ≤ m → E ⊆ D →
        h₀ ≤ Real.log ((2 : ℝ) ^ n) →
        B + 1 ≤ Real.log ((2 : ℝ) ^ m) - Real.log ((2 : ℝ) ^ n) →
        ∀ (o : E) (J : Finset E), o ∈ J →
        (∀ x ∈ J, squareProportionalBuffer δ a (2 ^ n) x) →
        (∀ x ∈ J, squareProportionalBuffer δ b (2 ^ m) x) →
        ∀ (hJ : J.Nonempty),
        let h := Real.log ((2 : ℝ) ^ n)
        let S := normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi))
        let ν := finiteGaussianMaximumResidualLaw (greenMatrix E)
          (finiteGaussianRegressionCov S o) J hJ (Real.sqrt (2 / Real.pi))
          (2 * h - (3 / 4 : ℝ) * Real.log h)
        ∀ a₀ v : ℝ, 0 < a₀ → 0 < v →
          ((gaussianReal 0 v.toNNReal).prod ν).real
            {p | a₀ ≤ max p.1 0 + p.2} ≤
          (gaussianReal 0 v.toNNReal).real (Ici a₀) +
          C * ((1 + a₀) * Real.exp (-2 * a₀ - c * a₀ ^ 2 / h)) +
          (C / Real.sqrt v) * (∫ z in Icc 0 a₀, (1 + z) *
            Real.exp (-(a₀ - z) ^ 2 / (2 * v) - 2 * z - c * z ^ 2 / h)) := by
  obtain ⟨C, c, h₀, B, hC, hc, hh₀, hB, hTail⟩ :=
    source_fine_residual_sum_tail hBDZ hSup sub_gaussian_positive_moment_input_internal hGreen δ hδ
    hδhalf
  refine ⟨C, c, h₀, B, hC, hc, hh₀, hB, ?_⟩
  intro D E a b m n hD hE hn hnm hED hh hgap o J ho hbuf hout hJ
  dsimp only
  intro a₀ v ha hv
  letI := finiteGaussianMaximumResidualLaw_isProbabilityMeasure (greenMatrix E)
    (finiteGaussianRegressionCov (normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi))) o)
    J hJ (Real.sqrt (2 / Real.pi))
    (2 * Real.log ((2 : ℝ) ^ n) - (3 / 4 : ℝ) * Real.log (Real.log ((2 : ℝ) ^ n)))
  have ht := source_upper_convolution_probability hConv _ a₀ v
    (Real.log ((2 : ℝ) ^ n)) c C ha hv
    (hTail D E a b m n hD hE hn hnm hED hh hgap o J ho hbuf hout hJ)
  convert ht using 1 <;> ring

end SRWTightness
