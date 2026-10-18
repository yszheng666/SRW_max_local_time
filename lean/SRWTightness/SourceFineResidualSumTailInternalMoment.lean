import SRWTightness.SubGaussianPositiveMomentInternal
import SRWTightness.PositiveConvolutionInternal
import SRWTightness.GaussianRegressionInternal
import SRWTightness.SourceBDZFineTail
import SRWTightness.SquareHarmonicResidualSupremum
import SRWTightness.ExternalBufferedSquareGreen
import SRWTightness.GaussianMaximumResidualTail

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- The actual independent fine/residual sum has the literal uniform tail in source(4.7). -/
theorem source_fine_residual_sum_tail_internal_moment (hBDZ : BDZDyadicSquareMaximumInput)
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
        ∀ z : ℝ, 0 ≤ z →
          ν.real (Ici z) ≤ C * (1 + z) * Real.exp (-2 * z - c * z ^ 2 / h) := by
  obtain ⟨C₀, L, B, hC₀, hL, hB, hGreenBound⟩ := hGreen δ hδ hδhalf
  obtain ⟨P, c, hP, hc, hFineBound⟩ := hBDZ
  obtain ⟨A, β, hA, hβ, hResBound⟩ := square_harmonic_residual_supremum hSup
    finite_gaussian_regression_input_internal L hL
  obtain ⟨C, hC, hSumBound⟩ := source_upper_actual_maxima_sum_tail
    positive_convolution_input_internal sub_gaussian_positive_moment_input_internal A β P c hA hβ
    hP.le hc.le
  refine ⟨C, c / 2, max 1 (2 * c / β), B, hC, by positivity,
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), hB, ?_⟩
  intro D E a b m n hD hE hn hnm hED hh₀ hgap o J ho hbuf hout hJ
  dsimp only
  have hh : 1 ≤ Real.log ((2 : ℝ) ^ n) := (le_max_left _ _).trans hh₀
  have hhpos : 0 < Real.log ((2 : ℝ) ^ n) := by linarith
  have hch : c / Real.log ((2 : ℝ) ^ n) ≤ β / 2 := by
    have hx := (le_max_right _ _).trans hh₀
    rw [div_le_iff₀ hhpos]
    have hy := (div_le_iff₀ hβ).mp hx
    nlinarith
  have he := hGreenBound D E a b m n hD hE hn hnm hED o o
    (hbuf o ho) (hbuf o ho) (hout o ho) (hout o ho)
  have hv : 0 < normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o := by
    have hb := abs_le.mp he.2.2
    linarith
  have hRes : ∀ u : ℝ, 0 ≤ u →
      (multivariateGaussian (0 : EuclideanSpace ℝ E)
        (finiteGaussianRegressionCov
          (normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi))) o)).real
        {φ | ∃ x ∈ J, u ≤ |φ x|} ≤ A * Real.exp (-β * u ^ 2) := by
    apply hResBound D E a (2 ^ n) hE (by positivity) hED J o
      (Real.sqrt (2 / Real.pi)) ho hv
    intro x hx y hy
    have hg := hGreenBound D E a b m n hD hE hn hnm hED x y
      (hbuf x hx) (hbuf y hy) (hout x hx) (hout y hy)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hg.2.1
  have hFine : ∀ u : ℝ, 1 ≤ u → (gaussianGreenLaw E E).real
      {φ | ∃ x ∈ J,
        2 * Real.log ((2 : ℝ) ^ n) - (3 / 4 : ℝ) *
          Real.log (Real.log ((2 : ℝ) ^ n)) + u ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
      P * (1 + u) * Real.exp (-2 * u - c * u ^ 2 / Real.log ((2 : ℝ) ^ n)) := by
    intro u hu
    subst E
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hFineBound a n hn u hu)
    rintro φ ⟨x, hx, hval⟩
    exact ⟨x, hval⟩
  intro z hz
  rw [finiteGaussianMaximumResidualLaw_tail]
  have hb := hSumBound E (greenMatrix E)
    (finiteGaussianRegressionCov (normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi))) o)
    J hJ (Real.sqrt (2 / Real.pi))
    (2 * Real.log ((2 : ℝ) ^ n) - (3 / 4 : ℝ) * Real.log (Real.log ((2 : ℝ) ^ n)))
    (Real.log ((2 : ℝ) ^ n)) hh hch hFine hRes z hz
  have hreal : -2 * z - c * z ^ 2 / (2 * Real.log ((2 : ℝ) ^ n)) =
      -2 * z - (c / 2) * z ^ 2 / Real.log ((2 : ℝ) ^ n) := by ring
  simpa only [hreal] using hb

end SRWTightness
