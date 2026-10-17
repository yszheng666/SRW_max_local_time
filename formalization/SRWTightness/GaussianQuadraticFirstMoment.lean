import SRWTightness.GaussianQuadraticTiltDensity

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The exact first moment under a quadratic Gaussian weight. -/
theorem gaussian_quadratic_first_moment (x s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    (∫ z : ℝ, z * Real.exp (-t * z ^ 2) ∂gaussianReal x s.toNNReal) =
      (x / (1 + 2 * s * t)) *
        (Real.exp (-t * x ^ 2 / (1 + 2 * s * t)) / Real.sqrt (1 + 2 * s * t)) := by
  have ha : 0 < 1 + 2 * s * t := by positivity
  have hv : s.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hs)
  have hv' : (s / (1 + 2 * s * t)).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (div_pos hs ha))
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have he (z : ℝ) : gaussianPDFReal x s.toNNReal z * (z * Real.exp (-t * z ^ 2)) =
      (Real.exp (-t * x ^ 2 / (1 + 2 * s * t)) / Real.sqrt (1 + 2 * s * t)) *
        (gaussianPDFReal (x / (1 + 2 * s * t))
          (s / (1 + 2 * s * t)).toNNReal z * z) := by
    calc
      _ = (gaussianPDFReal x s.toNNReal z * Real.exp (-t * z ^ 2)) * z := by ring
      _ = _ := by rw [gaussian_quadratic_tilt_density x s t z hs ht]; ring
  simp_rw [he]
  rw [integral_const_mul]
  have hmean := integral_gaussianReal_eq_integral_smul
    (μ := x / (1 + 2 * s * t)) (f := fun z : ℝ ↦ z) hv'
  rw [integral_id_gaussianReal] at hmean
  simp only [smul_eq_mul] at hmean
  rw [← hmean]
  ring

end SRWTightness
