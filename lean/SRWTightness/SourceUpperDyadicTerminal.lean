import SRWTightness.SourceUpperGreenTerminalProbability
import SRWTightness.NormalizedHarmonicResidualSupremum
import SRWTightness.ExternalBDZSquareMaximum

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The dyadic terminal estimate with both marginal tail premises discharged by named inputs. -/
theorem source_upper_dyadic_terminal (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (L G H V η B : ℝ)
    (hL : 0 < L) (hG : 0 < G) (hH : 0 < H) (hV : 0 < V)
    (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C κ h₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < h₀ ∧
      ∀ (D E : Finset Site) (a : Site) (n : ℕ), E = latticeSquareInterior a (2 ^ n) →
      2 ≤ n → ∀ (hED : E ⊆ D) (o : E) (J : Finset E) (K d h v q ε r : ℝ),
      o ∈ J → r = (2 : ℝ) ^ n → h = Real.log r → h₀ ≤ h →
      0 < normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o → 0 ≤ K →
      K ≤ normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o →
      (∀ x ∈ J, |normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) x o /
        normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o - 1| ≤
          K / normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o) →
      v = (1 + K / normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o) ^ 2 *
        normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o →
      (∀ x ∈ J, normSq ((x : Site) - (o : Site)) ≤ (G * r) ^ 2) →
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
  obtain ⟨A, b, hA, hb, hRes⟩ := normalized_harmonic_regression_residual_supremum
    hSup hReg L G hL hG
  obtain ⟨P, c, hP, hc, hFine⟩ := hBDZ
  obtain ⟨C, κ, hC, hκ, hTerminal⟩ := source_upper_green_terminal_probability
    hReg hSum hMoment hConv hMills hIntegral A b P c H V η B
      hA hb hP.le hc hH hV hη hB
  refine ⟨C, κ, max 1 (2 * c / b), hC, hκ, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro D E a n hE hn hED o J K d h v q ε r ho hr hlog hh₀ hv0 hK hKv hCoef hvScale
    hgeom hinc hd hhD hvD hhU hvU hscale herror hq hv hε
  have hh : 1 ≤ h := (le_max_left _ _).trans hh₀
  have hh0 : 0 < h := by linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hch : c / h ≤ b / 2 := by
    have hs : 2 * c / b ≤ h := (le_max_right _ _).trans hh₀
    have hs' := (div_le_iff₀ hb).mp hs
    apply (div_le_iff₀ hh0).mpr
    nlinarith only [hs']
  apply hTerminal D E hED o J ⟨o, ho⟩ (Real.sqrt (2 / Real.pi))
    (2 * h - (3 / 4 : ℝ) * Real.log h) K d h v q 0 ε r hv0 hK hKv hCoef hvScale
    hd hh hhD hvD hhU hvU hscale herror hq (by ring) hv (by linarith) hε hr0 hlog hch
  · intro u hu
    subst E
    have hf := hFine a n hn u hu
    rw [hlog, hr]
    refine LE.le.trans ?_ hf
    apply measureReal_mono _ (measure_ne_top _ _)
    rintro φ ⟨x, hx, ht⟩
    exact ⟨x, ht⟩
  · exact hRes D E hED J o r (Real.sqrt (2 / Real.pi)) ho hr0 hv0 hgeom hinc

end SRWTightness
