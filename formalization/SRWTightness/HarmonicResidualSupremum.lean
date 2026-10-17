import SRWTightness.ExternalPlanarGaussianSupremum
import SRWTightness.HarmonicGaussianRegression
import SRWTightness.Geometry

open MeasureTheory ProbabilityTheory Matrix
namespace SRWTightness

/-- Planar increment control gives a uniform tail for the actual harmonic regression residual. -/
theorem harmonic_regression_residual_supremum
    (hSup : PlanarGaussianIncrementSupInput) (hReg : FiniteGaussianRegressionInput)
    (L K : ℝ) (hL : 0 < L) (hK : 0 < K) :
    ∃ A b : ℝ, 0 < A ∧ 0 < b ∧ ∀ (D E : Finset Site) (hED : E ⊆ D)
      (J : Finset E) (o : E) (r : ℝ), o ∈ J → 0 < r →
      0 < (observationGreen D E - greenMatrix E) o o →
      (∀ x ∈ J, normSq ((x : Site) - (o : Site)) ≤ (K * r) ^ 2) →
      (∀ x ∈ J, ∀ y ∈ J,
        (observationGreen D E - greenMatrix E) x x +
          (observationGreen D E - greenMatrix E) y y -
          2 * (observationGreen D E - greenMatrix E) x y ≤
            L * normSq ((x : Site) - (y : Site)) / r ^ 2) →
      ∀ u : ℝ, 0 ≤ u →
        (multivariateGaussian (0 : EuclideanSpace ℝ E)
          (finiteGaussianRegressionCov (observationGreen D E - greenMatrix E) o)).real
            {φ | ∃ x ∈ J, u ≤ |φ x|} ≤ A * Real.exp (-b * u ^ 2) := by
  obtain ⟨A, b, hA, hb, hbound⟩ := hSup L K hL hK
  refine ⟨A, b, hA, hb, ?_⟩
  intro D E hED J o r ho hr hv hgeom hinc u hu
  let S := observationGreen D E - greenMatrix E
  let p : E → ℝ × ℝ := fun x ↦
    ((x.val.1 : ℝ) - (o.val.1 : ℝ), (x.val.2 : ℝ) - (o.val.2 : ℝ))
  apply hbound E (finiteGaussianRegressionCov S o) J o p r
    (harmonic_gaussian_regression hReg D E hED o hv).1 ho
    (finite_gaussian_regression_anchor S o hv) hr _ _ u hu
  · intro x hx
    simpa [p, normSq] using hgeom x hx
  · intro x hx y hy
    have hb := (finite_gaussian_regression_increment S o x y hv).trans (hinc x hx y hy)
    have he : normSq ((x : Site) - (y : Site)) =
        ((p x).1 - (p y).1) ^ 2 + ((p x).2 - (p y).2) ^ 2 := by
      simp [p, normSq]
      <;> ring
    simpa only [he] using hb

end SRWTightness
