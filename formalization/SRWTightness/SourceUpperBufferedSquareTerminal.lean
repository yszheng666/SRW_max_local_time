import SRWTightness.SourceUpperProportionalTerminal
import SRWTightness.ExternalBufferedSquareGreen

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The square terminal estimate from a bounded error for the original harmonic variance. -/
theorem source_upper_buffered_square_terminal (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ C κ d₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < d₀ ∧
      ∀ (D E : Finset Site) (a b : Site) (m n : ℕ),
      D = latticeSquareInterior b (2 ^ m) → E = latticeSquareInterior a (2 ^ n) →
      2 ≤ n → n ≤ m → ∀ (hED : E ⊆ D) (o : E) (J : Finset E) (d h q r : ℝ),
      o ∈ J → r = (2 : ℝ) ^ n → h = Real.log r → d₀ ≤ d →
      d = Real.log ((2 : ℝ) ^ m) →
      (∀ x ∈ J, squareProportionalBuffer δ a (2 ^ n) x) →
      (∀ x ∈ J, squareProportionalBuffer δ b (2 ^ m) x) →
      d / 8 ≤ h → h ≤ d / 2 → -Real.sqrt d ≤ q →
      (gaussianGreenLaw D E).real
        {φ | ∃ x ∈ J, 2 * d + q ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
        C * r ^ 2 * Real.exp (-2 * d) / d *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  obtain ⟨C₀, L, B, hC₀, hL, hB, hg⟩ := hGreen δ hδ hδhalf
  obtain ⟨C, κ, d₀, hC, hκ, hd₀, ht⟩ := source_upper_proportional_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral C₀ L B hC₀ hL hB
  refine ⟨C, κ, d₀, hC, hκ, hd₀, ?_⟩
  intro D E a b m n hD hE hn hnm hED o J d h q r ho hr hlog hd hdlog hbuf houter
    hhL hhU hq
  have hhlog : h = Real.log ((2 : ℝ) ^ n) := by rw [hlog, hr]
  apply ht D E a n hE hn hED o J d h q r ho hr hlog hd
  · intro x hx
    exact (hg D E a b m n hD hE hn hnm hED x o
      (hbuf x hx) (hbuf o ho) (houter x hx) (houter o ho)).1
  · intro x hx y hy
    simpa only [hr] using (hg D E a b m n hD hE hn hnm hED x y
      (hbuf x hx) (hbuf y hy) (houter x hx) (houter y hy)).2.1
  · exact hhL
  · exact hhU
  · exact hq
  · simpa only [hdlog, hhlog] using (hg D E a b m n hD hE hn hnm hED o o
      (hbuf o ho) (hbuf o ho) (houter o ho) (houter o ho)).2.2

end SRWTightness
