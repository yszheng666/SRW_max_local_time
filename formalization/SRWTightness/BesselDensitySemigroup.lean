import SRWTightness.KilledBrownianDensitySemigroup

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- At a positive intermediate location the two Doob factors cancel exactly. -/
theorem bessel_density_product_cancel (s t x y z : ℝ) (hx : x ≠ 0) (hz : z ≠ 0) :
    besselThreeDensity s x z * besselThreeDensity t z y =
      (y / x) * (killedBrownianDensity s x z * killedBrownianDensity t z y) := by
  unfold besselThreeDensity
  field_simp
  <;> ring

/-- The two-step Bessel density is integrable on the positive intermediate half-line. -/
theorem bessel_density_product_integrable (s t x y : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hx : 0 < x) :
    IntegrableOn (fun z ↦ besselThreeDensity s x z * besselThreeDensity t z y)
      (Set.Ioi (0 : ℝ)) := by
  apply ((killed_brownian_density_product_integrable s t x y hs ht).const_mul
    (y / x)).integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact (bessel_density_product_cancel s t x y z hx.ne' (ne_of_gt hz)).symm

/-- The literal Bessel transition kernels satisfy the Chapman–Kolmogorov identity. -/
theorem bessel_density_semigroup (s t x y : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hx : 0 < x) :
    (∫ z in Set.Ioi (0 : ℝ), besselThreeDensity s x z * besselThreeDensity t z y) =
      besselThreeDensity (s + t) x y := by
  calc
    _ = ∫ z in Set.Ioi (0 : ℝ), (y / x) *
        (killedBrownianDensity s x z * killedBrownianDensity t z y) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact bessel_density_product_cancel s t x y z hx.ne' (ne_of_gt hz)
    _ = _ := by
      rw [integral_const_mul, killed_brownian_density_semigroup s t x y hs ht]
      rfl

end SRWTightness
