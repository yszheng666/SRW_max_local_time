import SRWTightness.SourceUpperSquareTerminal
import SRWTightness.HarmonicVarianceError

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The square terminal estimate from a bounded error for the original harmonic variance. -/
theorem source_upper_square_variance_terminal (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (C₀ L H V η B : ℝ)
    (hC₀ : 0 ≤ C₀) (hL : 0 < L) (hH : 0 < H) (hV : 0 < V)
    (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C κ h₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < h₀ ∧
      ∀ (D E : Finset Site) (a : Site) (n : ℕ), E = latticeSquareInterior a (2 ^ n) →
      2 ≤ n → ∀ (hED : E ⊆ D) (o : E) (J : Finset E) (d h v q r : ℝ),
      o ∈ J → r = (2 : ℝ) ^ n → h = Real.log r → h₀ ≤ h →
      0 < normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o →
      C₀ + 4 * L ≤ normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o →
      (∀ x ∈ J, |normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) x x -
        normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o| ≤ C₀) →
      v = (1 + (C₀ + 4 * L) / normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o) ^ 2 *
        normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o →
      (∀ x ∈ J, ∀ y ∈ J,
        normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) x x +
          normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) y y -
          2 * normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) x y ≤
            L * normSq ((x : Site) - (y : Site)) / r ^ 2) →
      1 ≤ d → η * d ≤ h → η * d ≤ v → h ≤ H * d → v ≤ V * d →
      4 / η ^ 2 ≤ d → 6 * (B + 3 * (C₀ + 4 * L)) / η ≤ d → -Real.sqrt d ≤ q →
      |normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o - (d - h)| ≤ B →
      (gaussianGreenLaw D E).real
        {φ | ∃ x ∈ J, 2 * d + q ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
        C * r ^ 2 * Real.exp (-2 * d) / d *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  have hK : 0 ≤ C₀ + 4 * L := by positivity
  obtain ⟨C, κ, h₀, hC, hκ, hh₀, ht⟩ := source_upper_square_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral C₀ L H V η
      (B + 3 * (C₀ + 4 * L)) hC₀ hL hH hV hη (by positivity)
  refine ⟨C, κ, h₀, hC, hκ, hh₀, ?_⟩
  intro D E a n hE hn hED o J d h v q r ho hr hlog hh hv0 hKv hdiag hvScale
    hinc hd hhD hvD hhU hvU hscale herror hq herr
  have he := harmonic_enlarged_variance_error
    (normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o)
    (C₀ + 4 * L) d h B hv0 hK hKv herr
  rw [← hvScale] at he
  exact ht D E a n hE hn hED o J d h v q (v - (d - h)) r ho hr hlog hh
    hv0 hKv hdiag hvScale hinc hd hhD hvD hhU hvU hscale herror hq
    (by ring) (abs_le.mp he).2

end SRWTightness
