import SRWTightness.RadialLaplaceSubstitution

open MeasureTheory
namespace SRWTightness

/-- The dimension-three radial Laplace integral is integrable by its injective substitution. -/
theorem radial_laplace_integrable (s x : ℝ) (hs : 0 ≤ s) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ ↦
      Real.exp (-(t ^ 2) * x ^ 2 / (1 + 2 * s * t ^ 2)) /
        (Real.sqrt (1 + 2 * s * t ^ 2)) ^ 3) (Set.Ioi 0) := by
  let f : ℝ → ℝ := fun t ↦ t / Real.sqrt (1 + 2 * s * t ^ 2)
  let g : ℝ → ℝ := fun u ↦ Real.exp (-(x ^ 2) * u ^ 2)
  have hi : IntegrableOn g (f '' Set.Ioi 0) :=
    (integrable_exp_neg_mul_sq (sq_pos_of_pos hx)).integrableOn
  have he := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t _ ↦ (radial_laplace_substitution_deriv s t hs).hasDerivWithinAt)
    (radial_laplace_substitution_injective s hs).injOn g).mp hi
  apply he.congr
  filter_upwards [] with t
  have ha : 0 < 1 + 2 * s * t ^ 2 := by positivity
  rw [abs_of_nonneg (by positivity), smul_eq_mul]
  dsimp [g, f]
  rw [div_pow, Real.sq_sqrt ha.le]
  have harg : -(x ^ 2) * (t ^ 2 / (1 + 2 * s * t ^ 2)) =
      -(t ^ 2) * x ^ 2 / (1 + 2 * s * t ^ 2) := by ring
  rw [harg]
  ring

end SRWTightness
