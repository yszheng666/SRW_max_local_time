import SRWTightness.GaussianDensityConvolution
import SRWTightness.GaussianDensitySymmetry
import SRWTightness.BesselDensityLaplace
import SRWTightness.HalfLinePairIntegral

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The killed Brownian density is odd in its terminal spatial argument. -/
theorem killed_brownian_density_odd (s x y : ℝ) :
    killedBrownianDensity s x (-y) = -killedBrownianDensity s x y := by
  unfold killedBrownianDensity
  simp only [sub_neg_eq_add, ← sub_eq_add_neg]
  ring

/-- The product of killed kernels is integrable as a function of the intermediate location. -/
theorem killed_brownian_density_product_integrable (s t x y : ℝ)
    (hs : 0 < s) (ht : 0 < t) :
    Integrable (fun z ↦ killedBrownianDensity s x z * killedBrownianDensity t z y) := by
  have he (z : ℝ) : killedBrownianDensity s x z * killedBrownianDensity t z y =
      (gaussianPDFReal x s.toNNReal z * gaussianPDFReal y t.toNNReal z -
       gaussianPDFReal x s.toNNReal z * gaussianPDFReal (-y) t.toNNReal z) -
      (gaussianPDFReal (-x) s.toNNReal z * gaussianPDFReal y t.toNNReal z -
       gaussianPDFReal (-x) s.toNNReal z * gaussianPDFReal (-y) t.toNNReal z) := by
    rw [killedBrownianDensity_symm t z y, killed_brownian_density_gaussian s x z hs,
      killed_brownian_density_gaussian t y z ht]
    simp_rw [gaussian_density_reflect_mean]
    ring
  simp_rw [he]
  exact ((gaussian_density_product_integrable s t x y hs ht).sub
    (gaussian_density_product_integrable s t x (-y) hs ht)).sub
    ((gaussian_density_product_integrable s t (-x) y hs ht).sub
      (gaussian_density_product_integrable s t (-x) (-y) hs ht))

/-- The killed Brownian kernels compose at the sum of their elapsed times. -/
theorem killed_brownian_density_semigroup (s t x y : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (∫ z in Set.Ioi (0 : ℝ), killedBrownianDensity s x z * killedBrownianDensity t z y) =
      killedBrownianDensity (s + t) x y := by
  let f : ℝ → ℝ := fun z ↦ gaussianPDFReal x s.toNNReal z * killedBrownianDensity t y z
  have hfe (z : ℝ) : f z =
      gaussianPDFReal x s.toNNReal z * gaussianPDFReal y t.toNNReal z -
      gaussianPDFReal x s.toNNReal z * gaussianPDFReal (-y) t.toNNReal z := by
    dsimp [f]
    rw [killed_brownian_density_gaussian t y z ht, gaussian_density_reflect_mean]
    ring
  have hi : Integrable f := by
    change Integrable (fun z ↦ f z)
    simp_rw [hfe]
    exact (gaussian_density_product_integrable s t x y hs ht).sub
      (gaussian_density_product_integrable s t x (-y) hs ht)
  have hp (z : ℝ) :
      killedBrownianDensity s x z * killedBrownianDensity t z y = f z + f (-z) := by
    dsimp [f]
    rw [killedBrownianDensity_symm t z y, killed_brownian_density_gaussian s x z hs,
      killed_brownian_density_odd]
    ring
  simp_rw [hp]
  rw [half_line_pair_integral f hi]
  simp_rw [hfe]
  rw [integral_sub (gaussian_density_product_integrable s t x y hs ht)
      (gaussian_density_product_integrable s t x (-y) hs ht),
    gaussian_density_convolution s t x y hs ht,
    gaussian_density_convolution s t x (-y) hs ht,
    killed_brownian_density_gaussian (s + t) x y (add_pos hs ht)]

end SRWTightness
