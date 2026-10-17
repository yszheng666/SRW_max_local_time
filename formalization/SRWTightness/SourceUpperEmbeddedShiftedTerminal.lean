import SRWTightness.SourceUpperBufferedShiftedTerminal
import SRWTightness.GaussianObservationDomainComparison

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The square terminal estimate from a bounded error for the original harmonic variance. -/
theorem source_upper_embedded_shifted_terminal (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (δ A : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hA : 0 ≤ A) :
    ∃ C κ d₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < d₀ ∧
      ∀ (D K E : Finset Site) (a b : Site) (m n : ℕ),
      D = latticeSquareInterior b (2 ^ m) → E = latticeSquareInterior a (2 ^ n) →
      2 ≤ n → n ≤ m → ∀ (hEK : E ⊆ K) (hKD : K ⊆ D) (o : E) (J : Finset E) (d h q r : ℝ),
      o ∈ J → r = (2 : ℝ) ^ n → h = Real.log r → d₀ ≤ d →
      |d - Real.log ((2 : ℝ) ^ m)| ≤ A →
      (∀ x ∈ J, squareProportionalBuffer δ a (2 ^ n) x) →
      (∀ x ∈ J, squareProportionalBuffer δ b (2 ^ m) x) →
      d / 8 ≤ h → h ≤ d / 2 → -Real.sqrt d ≤ q →
      (gaussianGreenLaw K E).real
        {φ | ∃ x ∈ J, 2 * d + q ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
        C * r ^ 2 * Real.exp (-2 * d) / d *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  obtain ⟨C, κ, d₀, hC, hκ, hd₀, ht⟩ := source_upper_buffered_shifted_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen δ A hδ hδhalf hA
  refine ⟨2 * C, κ, d₀, by positivity, hκ, hd₀, ?_⟩
  intro D K E a b m n hD hE hn hnm hEK hKD o J d h q r ho hr hlog hd hdlog
    hbuf houter hhL hhU hq
  have hb := ht D E a b m n hD hE hn hnm (hEK.trans hKD) o J d h q r
    ho hr hlog hd hdlog hbuf houter hhL hhU hq
  have hσ : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hc := gaussian_normalized_observation_domain_comparison D K E hEK hKD J
    (Real.sqrt (2 / Real.pi)) (2 * d + q) hσ
  calc
    _ ≤ 2 * (gaussianGreenLaw D E).real
        {φ | ∃ x ∈ J, 2 * d + q ≤ φ x / Real.sqrt (2 / Real.pi)} := hc
    _ ≤ 2 * (C * r ^ 2 * Real.exp (-2 * d) / d *
        Real.exp (-2 * q - κ * (max q 0) ^ 2 / d)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

end SRWTightness
