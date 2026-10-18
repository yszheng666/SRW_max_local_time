import SRWTightness.NormalizedHarmonicReconstruction

namespace SRWTightness

/-- The source Gaussian normalization multiplies every actual Green difference by pi over two. -/
theorem normalizedHarmonicCov_source_apply (D E : Finset Site) (x y : E) :
    normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) x y =
      (Real.pi / 2) * (killedGreen D x y - killedGreen E x y) := by
  change (Real.sqrt (2 / Real.pi))⁻¹ ^ 2 *
    (killedGreen D x y - killedGreen E x y) = _
  rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / Real.pi), inv_div]

end SRWTightness
