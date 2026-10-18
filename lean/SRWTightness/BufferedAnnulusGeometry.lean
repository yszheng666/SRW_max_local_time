import SRWTightness.GeometricRadiusLogError
import SRWTightness.AnnulusExitGeometry

namespace SRWTightness

/-- The entire buffered middle layer lies between the actual inner and outer radii. -/
theorem buffered_middle_annulus_geometry (ρ H : ℝ) (hH : 1 ≤ H) (hρ : 8 * H ≤ ρ)
    (x : Site) (hx : |Real.sqrt (normSq x) - Real.exp 1 * ρ| ≤ 2 * H) :
    2 ≤ ρ - H ∧ ρ - H ≤ Real.exp 2 * ρ + H ∧
      (ρ - H) ^ 2 ≤ normSq x ∧ normSq x ≤ (Real.exp 2 * ρ + H) ^ 2 := by
  have hρ0 : 0 < ρ := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have hegap : Real.exp 1 + 1 ≤ Real.exp 2 := by rw [he2]; nlinarith
  have hmid : 2 * ρ ≤ Real.exp 1 * ρ := by nlinarith
  have hout : Real.exp 1 * ρ + ρ ≤ Real.exp 2 * ρ := by
    nlinarith [mul_le_mul_of_nonneg_right hegap hρ0.le]
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  have hs := Real.sq_sqrt (normSq_nonneg x)
  have hs0 := Real.sqrt_nonneg (normSq x)
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · have hl : ρ - H ≤ Real.sqrt (normSq x) := by linarith
    nlinarith
  · have hu : Real.sqrt (normSq x) ≤ Real.exp 2 * ρ + H := by linarith
    nlinarith

/-- Both source middle boundary layers fit the common buffer used in the probability estimate. -/
theorem middle_boundary_layers_in_buffer (r ρ H : ℝ) (hH : 1 ≤ H)
    (hr : (Real.exp 1 * ρ - H - 1 ≤ r ∧ r ≤ Real.exp 1 * ρ - H) ∨
      (Real.exp 1 * ρ + H ≤ r ∧ r ≤ Real.exp 1 * ρ + H + 1)) :
    |r - Real.exp 1 * ρ| ≤ 2 * H := by
  apply abs_le.mpr
  rcases hr with ⟨hl, hu⟩ | ⟨hl, hu⟩ <;> constructor <;> linarith

end SRWTightness
