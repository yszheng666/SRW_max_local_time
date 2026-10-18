import SRWTightness.SourceUpperSquareVarianceTerminal
import SRWTightness.SourceUpperVarianceScales

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The square terminal estimate from a bounded error for the original harmonic variance. -/
theorem source_upper_proportional_terminal (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (C₀ L B : ℝ)
    (hC₀ : 0 ≤ C₀) (hL : 0 < L) (hB : 0 ≤ B) :
    ∃ C κ d₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < d₀ ∧
      ∀ (D E : Finset Site) (a : Site) (n : ℕ), E = latticeSquareInterior a (2 ^ n) →
      2 ≤ n → ∀ (hED : E ⊆ D) (o : E) (J : Finset E) (d h q r : ℝ),
      o ∈ J → r = (2 : ℝ) ^ n → h = Real.log r → d₀ ≤ d →
      (∀ x ∈ J, |normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) x x -
        normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o| ≤ C₀) →
      (∀ x ∈ J, ∀ y ∈ J,
        normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) x x +
          normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) y y -
          2 * normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) x y ≤
            L * normSq ((x : Site) - (y : Site)) / r ^ 2) →
      d / 8 ≤ h → h ≤ d / 2 → -Real.sqrt d ≤ q →
      |normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o - (d - h)| ≤ B →
      (gaussianGreenLaw D E).real
        {φ | ∃ x ∈ J, 2 * d + q ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
        C * r ^ 2 * Real.exp (-2 * d) / d *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  have hK : 0 ≤ C₀ + 4 * L := by positivity
  have hB' : 0 ≤ B + 3 * (C₀ + 4 * L) := by positivity
  obtain ⟨C, κ, h₀, hC, hκ, hh₀, ht⟩ := source_upper_square_variance_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral C₀ L (1 / 2) 2 (1 / 8) B
      hC₀ hL (by norm_num) (by norm_num) (by norm_num) hB
  refine ⟨C, κ, max 256 (max (48 * (B + 3 * (C₀ + 4 * L))) (8 * h₀)),
    hC, hκ, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro D E a n hE hn hED o J d h q r ho hr hlog hd₀ hdiag hinc hhL hhU hq herr
  have hd256 : 256 ≤ d := (le_max_left _ _).trans hd₀
  have hdB : 48 * (B + 3 * (C₀ + 4 * L)) ≤ d :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hd₀)
  have hdh : 8 * h₀ ≤ d :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hd₀)
  have hs := source_upper_variance_scales d h
    (normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o)
    (C₀ + 4 * L) B (by linarith) hhL hhU hK hB (by linarith) herr
  apply ht D E a n hE hn hED o J d h _ q r ho hr hlog (by linarith)
    hs.1 hs.2.1 hdiag rfl hinc (by linarith)
  · linarith
  · linarith [hs.2.2.1]
  · linarith
  · exact hs.2.2.2.1
  · norm_num
    exact hd256
  · norm_num
    linarith
  · exact hq
  · exact herr

end SRWTightness
