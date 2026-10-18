import SRWTightness.GaussianFuturePathIndependence
import SRWTightness.GaussianFuturePathCovariance
import SRWTightness.ScaledGaussianPathLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The whole future increment path has the actual Brownian law for the remaining duration. -/
theorem gaussian_future_path_law (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    gaussianCoefficientLaw.map (fun ω (t : Set.Icc (0 : ℝ) (1 - s)) ↦
      gaussianDyadicPath ω (s + t) - gaussianDyadicPath ω s) =
    gaussianCoefficientLaw.map (fun ω (t : Set.Icc (0 : ℝ) (1 - s)) ↦
      Real.sqrt (1 - s) * gaussianDyadicPath ω (t / (1 - s))) := by
  have hT : 0 < 1 - s := sub_pos.mpr hs1
  let j : Set.Icc (0 : ℝ) (1 - s) →
      Set.Icc (0 : ℝ) s ⊕ Set.Icc s (1 : ℝ) := fun t ↦
    Sum.inr ⟨s + t, by linarith [t.property.1], by linarith [t.property.2]⟩
  have hg := (gaussian_past_future_path_gaussian s hs hs1.le).comp_right j
  apply gaussian_cross_space_process_law_eq gaussianCoefficientLaw gaussianCoefficientLaw _ _
    hg (scaled_gaussian_path_process (1 - s) hT)
  · exact measurable_pi_lambda _ (fun t ↦
      (gaussianDyadicPath_measurable _).sub (gaussianDyadicPath_measurable _))
  · exact measurable_pi_lambda _ (fun t ↦
      measurable_const.mul (gaussianDyadicPath_measurable _))
  · intro t
    change (∫ ω, gaussianDyadicPath ω (s + t) - gaussianDyadicPath ω s
      ∂gaussianCoefficientLaw) = _
    rw [gaussian_path_increment_mean s (s + t) hs (by linarith [t.property.1])
      (by linarith [t.property.2]), integral_const_mul,
      (gaussianPath_eval_hasLaw (t / (1 - s)) (div_nonneg t.property.1 hT.le)
        ((div_le_one hT).mpr t.property.2)).integral_eq,
      integral_id_gaussianReal, mul_zero]
  · intro u v
    change cov[fun ω ↦ gaussianDyadicPath ω (s + u) - gaussianDyadicPath ω s,
      fun ω ↦ gaussianDyadicPath ω (s + v) - gaussianDyadicPath ω s;
      gaussianCoefficientLaw] = _
    rw [gaussian_future_path_covariance s u v hs u.property.1 v.property.1
      (by linarith [u.property.2]) (by linarith [v.property.2]),
      scaled_gaussian_path_covariance (1 - s) u v hT u.property.1 u.property.2
        v.property.1 v.property.2]

end SRWTightness
