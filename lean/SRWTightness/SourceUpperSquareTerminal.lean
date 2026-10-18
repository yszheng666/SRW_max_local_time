import SRWTightness.SourceUpperDyadicTerminal
import SRWTightness.SquareHarmonicRegressionBounds

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The dyadic terminal estimate with both marginal tail premises discharged by named inputs. -/
theorem source_upper_square_terminal (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (C₀ L H V η B : ℝ)
    (hC₀ : 0 ≤ C₀) (hL : 0 < L) (hH : 0 < H) (hV : 0 < V)
    (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C κ h₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < h₀ ∧
      ∀ (D E : Finset Site) (a : Site) (n : ℕ), E = latticeSquareInterior a (2 ^ n) →
      2 ≤ n → ∀ (hED : E ⊆ D) (o : E) (J : Finset E) (d h v q ε r : ℝ),
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
      4 / η ^ 2 ≤ d → 6 * B / η ≤ d → -Real.sqrt d ≤ q →
      v = d - h + ε → ε ≤ B →
      (gaussianGreenLaw D E).real
        {φ | ∃ x ∈ J, 2 * d + q ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
        C * r ^ 2 * Real.exp (-2 * d) / d *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  obtain ⟨C, κ, h₀, hC, hκ, hh₀, ht⟩ := source_upper_dyadic_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral L 2 H V η B
      hL (by norm_num) hH hV hη hB
  refine ⟨C, κ, h₀, hC, hκ, hh₀, ?_⟩
  intro D E a n hE hn hED o J d h v q ε r ho hr hlog hh hv0 hKv hdiag hvScale
    hinc hd hhD hvD hhU hvU hscale herror hq hv hε
  have hN : 0 < (2 : ℕ) ^ n := by positivity
  have hcast : ((2 ^ n : ℕ) : ℝ) = r := by simp [hr]
  apply ht D E a n hE hn hED o J (C₀ + 4 * L) d h v q ε r ho hr hlog hh
    hv0 (by positivity) hKv ?_ hvScale ?_ hinc hd hhD hvD hhU hvU hscale herror hq hv hε
  · intro x hx
    apply square_harmonic_regression_coefficient D E hED a (2 ^ n) hE hN
      (Real.sqrt (2 / Real.pi)) o x C₀ L hC₀ hL.le hv0 (hdiag x hx)
    simpa only [hcast] using hinc x hx o ho
  · intro x hx
    rw [← hcast]
    apply latticeSquareInterior_planar_bound a x o (2 ^ n)
    · rw [← hE]
      exact x.property
    · rw [← hE]
      exact o.property

end SRWTightness
