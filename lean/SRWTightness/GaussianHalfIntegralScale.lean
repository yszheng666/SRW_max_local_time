import SRWTightness.GaussianSymmetricInterval

open MeasureTheory
namespace SRWTightness

/-- Scaling the positive Gaussian integral matches the radial Laplace image interval. -/
theorem gaussian_half_integral_scale (s x : ℝ) (hs : 0 < s) :
    (∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2) / (2 * s))) =
      (x * Real.sqrt (2 * s)) *
        ∫ u in (0 : ℝ)..(1 / Real.sqrt (2 * s)), Real.exp (-(x ^ 2) * u ^ 2) := by
  have hS : 0 < Real.sqrt (2 * s) := Real.sqrt_pos.mpr (by positivity)
  have hSq := Real.sq_sqrt (by positivity : 0 ≤ 2 * s)
  have he := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ ↦ Real.exp (-(t ^ 2) / (2 * s)))
    (a := (0 : ℝ)) (b := 1 / Real.sqrt (2 * s)) (x * Real.sqrt (2 * s))
  have harg (u : ℝ) : -((x * Real.sqrt (2 * s) * u) ^ 2) / (2 * s) =
      -(x ^ 2) * u ^ 2 := by
    rw [mul_pow, mul_pow, hSq]
    field_simp [ne_of_gt hs]
    <;> ring
  simp only [harg, smul_eq_mul, mul_zero] at he
  have hend : x * Real.sqrt (2 * s) * (1 / Real.sqrt (2 * s)) = x := by
    field_simp [ne_of_gt hS]
  rw [hend] at he
  exact he.symm

end SRWTightness
