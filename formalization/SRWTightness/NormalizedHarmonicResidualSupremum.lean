import SRWTightness.ExternalPlanarGaussianSupremum
import SRWTightness.NormalizedHarmonicReconstruction
import SRWTightness.Geometry

open MeasureTheory ProbabilityTheory Matrix
namespace SRWTightness

/-- Planar increments control the actual normalized harmonic regression residual. -/
theorem normalized_harmonic_regression_residual_supremum
    (hSup : PlanarGaussianIncrementSupInput) (hReg : FiniteGaussianRegressionInput)
    (L K : ℝ) (hL : 0 < L) (hK : 0 < K) :
    ∃ A b : ℝ, 0 < A ∧ 0 < b ∧ ∀ (D E : Finset Site) (hED : E ⊆ D)
      (J : Finset E) (o : E) (r σ : ℝ), o ∈ J → 0 < r →
      0 < (normalizedHarmonicCov D E σ) o o →
      (∀ x ∈ J, normSq ((x : Site) - (o : Site)) ≤ (K * r) ^ 2) →
      (∀ x ∈ J, ∀ y ∈ J,
        (normalizedHarmonicCov D E σ) x x +
          (normalizedHarmonicCov D E σ) y y -
          2 * (normalizedHarmonicCov D E σ) x y ≤
            L * normSq ((x : Site) - (y : Site)) / r ^ 2) →
      ∀ u : ℝ, 0 ≤ u →
        (multivariateGaussian (0 : EuclideanSpace ℝ E)
          (finiteGaussianRegressionCov (normalizedHarmonicCov D E σ) o)).real
            {φ | ∃ x ∈ J, u ≤ |φ x|} ≤ A * Real.exp (-b * u ^ 2) := by
  obtain ⟨A, b, hA, hb, hbound⟩ := hSup L K hL hK
  refine ⟨A, b, hA, hb, ?_⟩
  intro D E hED J o r σ ho hr hv hgeom hinc u hu
  let S := normalizedHarmonicCov D E σ
  let p : E → ℝ × ℝ := fun x ↦
    ((x.val.1 : ℝ) - (o.val.1 : ℝ), (x.val.2 : ℝ) - (o.val.2 : ℝ))
  apply hbound E (finiteGaussianRegressionCov S o) J o p r
    (hReg E S o (normalizedHarmonicCov_posSemidef D E hED σ) hv).1 ho
    (finite_gaussian_regression_anchor S o hv) hr _ _ u hu
  · intro x hx
    simpa [p, normSq] using hgeom x hx
  · intro x hx y hy
    have hb := (finite_gaussian_regression_increment S o x y hv).trans (hinc x hx y hy)
    have he : normSq ((x : Site) - (y : Site)) =
        ((p x).1 - (p y).1) ^ 2 + ((p x).2 - (p y).2) ^ 2 := by
      simp [p, normSq]
    simpa only [he] using hb

end SRWTightness
