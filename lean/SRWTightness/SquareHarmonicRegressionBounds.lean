import SRWTightness.LatticeSquareDiameter
import SRWTightness.GaussianIncrementNonnegative
import SRWTightness.NormalizedHarmonicReconstruction

namespace SRWTightness

/-- Square geometry turns diagonal and increment estimates into uniform regression coefficients. -/
theorem square_harmonic_regression_coefficient (D E : Finset Site) (hED : E ⊆ D)
    (a : Site) (N : ℕ) (hE : E = latticeSquareInterior a N) (hN : 0 < N)
    (σ : ℝ) (o x : E) (C₀ L : ℝ) (hC₀ : 0 ≤ C₀) (hL : 0 ≤ L)
    (hv : 0 < normalizedHarmonicCov D E σ o o)
    (hdiag : |normalizedHarmonicCov D E σ x x - normalizedHarmonicCov D E σ o o| ≤ C₀)
    (hinc : normalizedHarmonicCov D E σ x x + normalizedHarmonicCov D E σ o o -
      2 * normalizedHarmonicCov D E σ x o ≤
        L * normSq ((x : Site) - (o : Site)) / (N : ℝ) ^ 2) :
    |normalizedHarmonicCov D E σ x o / normalizedHarmonicCov D E σ o o - 1| ≤
      (C₀ + 4 * L) / normalizedHarmonicCov D E σ o o := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : normSq ((x : Site) - (o : Site)) ≤ (2 * (N : ℝ)) ^ 2 := by
    apply latticeSquareInterior_planar_bound a x o N
    · rw [← hE]
      exact x.property
    · rw [← hE]
      exact o.property
  have hi : L * normSq ((x : Site) - (o : Site)) / (N : ℝ) ^ 2 ≤ 4 * L := by
    apply (div_le_iff₀ (sq_pos_of_pos hN0)).mpr
    have hm := mul_le_mul_of_nonneg_left hd hL
    nlinarith only [hm]
  apply covariance_regression_coefficient_bound _
    (normalizedHarmonicCov_posSemidef D E hED σ) o x (C₀ + 4 * L) hv
  · exact hdiag.trans (le_add_of_nonneg_right (by positivity))
  · exact (hinc.trans hi).trans (le_add_of_nonneg_left hC₀)

end SRWTightness
