import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open MeasureTheory
namespace SRWTightness

/-- The inverse square root has an exact positive Gaussian integral representation. -/
theorem inverse_sqrt_gaussian_integral (a : ℝ) (ha : 0 < a) :
    (Real.sqrt a)⁻¹ = (2 / Real.sqrt Real.pi) *
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-a * t ^ 2) := by
  rw [integral_gaussian_Ioi, Real.sqrt_div Real.pi_pos.le]
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp

/-- The radial inverse is represented by the product of the three coordinate Laplace weights. -/
theorem radial_inverse_gaussian_integral (x y z : ℝ)
    (h : 0 < x ^ 2 + y ^ 2 + z ^ 2) :
    (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2))⁻¹ = (2 / Real.sqrt Real.pi) *
      ∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(t ^ 2) * x ^ 2) * Real.exp (-(t ^ 2) * y ^ 2) *
          Real.exp (-(t ^ 2) * z ^ 2) := by
  rw [inverse_sqrt_gaussian_integral _ h]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end SRWTightness
