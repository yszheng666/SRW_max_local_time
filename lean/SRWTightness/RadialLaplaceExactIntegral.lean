import SRWTightness.RadialLaplaceRange

open MeasureTheory
namespace SRWTightness

/-- The full radial Laplace integral equals a Gaussian integral over the exact image interval. -/
theorem radial_laplace_integral_exact (s x : ℝ) (hs : 0 < s) :
    (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(t ^ 2) * x ^ 2 / (1 + 2 * s * t ^ 2)) /
        (Real.sqrt (1 + 2 * s * t ^ 2)) ^ 3) =
      ∫ u in Set.Ioo 0 (1 / Real.sqrt (2 * s)), Real.exp (-(x ^ 2) * u ^ 2) := by
  let f : ℝ → ℝ := fun t ↦ t / Real.sqrt (1 + 2 * s * t ^ 2)
  let g : ℝ → ℝ := fun u ↦ Real.exp (-(x ^ 2) * u ^ 2)
  have he := integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t _ ↦ (radial_laplace_substitution_deriv s t hs.le).hasDerivWithinAt)
    (radial_laplace_substitution_injective s hs.le).injOn g
  have hfun (t : ℝ) :
      |(Real.sqrt (1 + 2 * s * t ^ 2))⁻¹ ^ 3| • g (f t) =
        Real.exp (-(t ^ 2) * x ^ 2 / (1 + 2 * s * t ^ 2)) /
          (Real.sqrt (1 + 2 * s * t ^ 2)) ^ 3 := by
    have ha : 0 < 1 + 2 * s * t ^ 2 := by positivity
    rw [abs_of_nonneg (by positivity), smul_eq_mul]
    dsimp [g, f]
    rw [div_pow, Real.sq_sqrt ha.le]
    have harg : -(x ^ 2) * (t ^ 2 / (1 + 2 * s * t ^ 2)) =
        -(t ^ 2) * x ^ 2 / (1 + 2 * s * t ^ 2) := by ring
    rw [harg]
    ring
  change (∫ u in f '' Set.Ioi 0, g u) =
    ∫ t in Set.Ioi 0, |(Real.sqrt (1 + 2 * s * t ^ 2))⁻¹ ^ 3| • g (f t) at he
  simp_rw [hfun] at he
  rw [radial_laplace_substitution_image s hs] at he
  exact he.symm

end SRWTightness
