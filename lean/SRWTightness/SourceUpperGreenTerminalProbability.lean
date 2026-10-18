import SRWTightness.SourceUpperGreenFieldComparison
import SRWTightness.SourceUpperFineMaximumTail
import SRWTightness.GaussianMaximumResidualTail
import SRWTightness.SourceUpperTerminalSumProbability

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- The actual Green-field terminal bound from marginal tail estimates and scale data. -/
theorem source_upper_green_terminal_probability (hReg : FiniteGaussianRegressionInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (A b P c H V η B : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hP : 0 ≤ P) (hc : 0 < c)
    (hH : 0 < H) (hV : 0 < V) (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ (D E : Finset Site) (hED : E ⊆ D)
      (o : E) (J : Finset E) (hJ : J.Nonempty) (σ m K d h v q δ ε r : ℝ),
      0 < normalizedHarmonicCov D E σ o o → 0 ≤ K →
      K ≤ normalizedHarmonicCov D E σ o o →
      (∀ x ∈ J, |normalizedHarmonicCov D E σ x o /
        normalizedHarmonicCov D E σ o o - 1| ≤ K / normalizedHarmonicCov D E σ o o) →
      v = (1 + K / normalizedHarmonicCov D E σ o o) ^ 2 *
        normalizedHarmonicCov D E σ o o →
      1 ≤ d → 1 ≤ h → η * d ≤ h → η * d ≤ v → h ≤ H * d → v ≤ V * d →
      4 / η ^ 2 ≤ d → 6 * B / η ≤ d → -Real.sqrt d ≤ q →
      m = 2 * h - (3 / 4 : ℝ) * Real.log h - δ →
      v = d - h + ε → -B ≤ δ → ε ≤ B → 0 < r → h = Real.log r → c / h ≤ b / 2 →
      (∀ u : ℝ, 1 ≤ u → (gaussianGreenLaw E E).real
        {φ | ∃ x ∈ J, m + u ≤ φ x / σ} ≤
          P * (1 + u) * Real.exp (-2 * u - c * u ^ 2 / h)) →
      (∀ u : ℝ, 0 ≤ u →
        (multivariateGaussian (0 : EuclideanSpace ℝ E)
          (finiteGaussianRegressionCov (normalizedHarmonicCov D E σ) o)).real
          {φ | ∃ x ∈ J, u ≤ |φ x|} ≤ A * Real.exp (-b * u ^ 2)) →
      (gaussianGreenLaw D E).real {φ | ∃ x ∈ J, 2 * d + q ≤ φ x / σ} ≤
        C * r ^ 2 * Real.exp (-2 * d) / d *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  obtain ⟨R, hR, hResidual⟩ := source_upper_actual_maxima_sum_tail hSum hMoment
    A b P c hA hb hP hc.le
  obtain ⟨C, κ, hC, hκ, hTerminal⟩ := source_upper_terminal_sum_probability hConv hMills
    hIntegral (c / 2) H V η B R (by positivity) hH hV hη hB hR.le
  refine ⟨C, κ, hC, hκ, ?_⟩
  intro D E hED o J hJ σ m K d h v q δ ε r hv0 hK hKv hCoef hvScale
    hd hh hhD hvD hhU hvU hscale herror hq hm hv hδ hε hr hlog hch hFine hRes
  let ν := finiteGaussianMaximumResidualLaw (greenMatrix E)
    (finiteGaussianRegressionCov (normalizedHarmonicCov D E σ) o) J hJ σ m
  letI : IsProbabilityMeasure ν := finiteGaussianMaximumResidualLaw_isProbabilityMeasure _ _ _ _ _ _
  have hTail : ∀ z : ℝ, 0 ≤ z → ν.real (Ici z) ≤
      R * (1 + z) * Real.exp (-2 * z - (c / 2) * z ^ 2 / h) := by
    intro z hz
    rw [show ν = finiteGaussianMaximumResidualLaw (greenMatrix E)
      (finiteGaussianRegressionCov (normalizedHarmonicCov D E σ) o) J hJ σ m from rfl,
      finiteGaussianMaximumResidualLaw_tail]
    have ht := hResidual E (greenMatrix E)
      (finiteGaussianRegressionCov (normalizedHarmonicCov D E σ) o)
      J hJ σ m h hh hch hFine hRes z hz
    have he : -2 * z - c * z ^ 2 / (2 * h) = -2 * z - (c / 2) * z ^ 2 / h := by ring
    simpa only [he] using ht
  have ha : 2 * d + q - m = 2 * (d - h) + q + (3 / 4 : ℝ) * Real.log h + δ := by
    rw [hm]
    ring
  have ht := hTerminal ν (2 * d + q - m) d h v q δ ε r
    hd hh hhD hvD hhU hvU hscale herror hq ha hv hδ hε hr hlog hTail
  have hg := source_upper_green_field_comparison hReg D E hED o J hJ σ m K (2 * d + q)
    hv0 hK hKv hCoef
  rw [← hvScale] at hg
  exact hg.trans ht

end SRWTightness
