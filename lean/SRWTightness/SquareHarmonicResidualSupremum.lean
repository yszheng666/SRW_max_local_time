import SRWTightness.LatticeSquareDiameter
import SRWTightness.NormalizedHarmonicResidualSupremum

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Square geometry supplies the diameter condition for the actual residual tail. -/
theorem square_harmonic_residual_supremum (hSup : PlanarGaussianIncrementSupInput)
    (hReg : FiniteGaussianRegressionInput) (L : ℝ) (hL : 0 < L) :
    ∃ A b : ℝ, 0 < A ∧ 0 < b ∧ ∀ (D E : Finset Site) (a : Site) (N : ℕ),
      E = latticeSquareInterior a N → 0 < N → ∀ (hED : E ⊆ D)
      (J : Finset E) (o : E) (σ : ℝ), o ∈ J →
      0 < normalizedHarmonicCov D E σ o o →
      (∀ x ∈ J, ∀ y ∈ J,
        normalizedHarmonicCov D E σ x x + normalizedHarmonicCov D E σ y y -
          2 * normalizedHarmonicCov D E σ x y ≤
            L * normSq ((x : Site) - (y : Site)) / (N : ℝ) ^ 2) →
      ∀ u : ℝ, 0 ≤ u →
        (multivariateGaussian (0 : EuclideanSpace ℝ E)
          (finiteGaussianRegressionCov (normalizedHarmonicCov D E σ) o)).real
            {φ | ∃ x ∈ J, u ≤ |φ x|} ≤ A * Real.exp (-b * u ^ 2) := by
  obtain ⟨A, b, hA, hb, hBound⟩ := normalized_harmonic_regression_residual_supremum
    hSup hReg L 2 hL (by norm_num)
  refine ⟨A, b, hA, hb, ?_⟩
  intro D E a N hE hN hED J o σ ho hv hinc u hu
  apply hBound D E hED J o (N : ℝ) σ ho (by exact_mod_cast hN) hv _ hinc u hu
  intro x _
  apply latticeSquareInterior_planar_bound a x o N
  · rw [← hE]
    exact x.property
  · rw [← hE]
    exact o.property

end SRWTightness
