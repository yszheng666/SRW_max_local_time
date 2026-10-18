import SRWTightness.GaussianPathIncrementLaw
import SRWTightness.ExternalBesselThree

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Each scaled Brownian coordinate increment has variance equal to its elapsed physical time. -/
theorem bessel_scaled_increment_law (T r t : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T) :
    HasLaw (fun ω ↦ Real.sqrt T *
      (gaussianDyadicPath ω (t / T) - gaussianDyadicPath ω (r / T)))
      (gaussianReal 0 (t - r).toNNReal) gaussianCoefficientLaw := by
  have hl := gaussian_path_increment_law (r / T) (t / T)
    (div_nonneg hr hT.le) ((div_le_div_iff_of_pos_right hT).mpr hrt)
    ((div_le_one hT).mpr ht)
  have hv : NNReal.mk ((Real.sqrt T) ^ 2) (sq_nonneg _) *
      (t / T - r / T).toNNReal = (t - r).toNNReal := by
    apply Subtype.ext
    change (Real.sqrt T) ^ 2 * max (t / T - r / T) 0 = max (t - r) 0
    rw [Real.sq_sqrt hT.le, max_eq_left (sub_nonneg.mpr
      ((div_le_div_iff_of_pos_right hT).mpr hrt)), max_eq_left (sub_nonneg.mpr hrt)]
    field_simp
    <;> ring
  simpa only [mul_zero, hv] using gaussianReal_const_mul hl (Real.sqrt T)

/-- The three actual scaled coordinate increments have the independent Gaussian vector law. -/
theorem bessel_vector_increment_law (T r t : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T) :
    HasLaw (fun ω : Fin 3 → GaussianCoefficientSpace ↦ fun i ↦ Real.sqrt T *
      (gaussianDyadicPath (ω i) (t / T) - gaussianDyadicPath (ω i) (r / T)))
      (Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 (t - r).toNNReal))
      (independentBridgeLaw (Fin 3)) := by
  have hm : Measurable (fun ω ↦ Real.sqrt T *
      (gaussianDyadicPath ω (t / T) - gaussianDyadicPath ω (r / T))) :=
    measurable_const.mul ((gaussianDyadicPath_measurable _).sub (gaussianDyadicPath_measurable _))
  exact (iIndepFun_infinitePi (fun _ : Fin 3 ↦ hm)).hasLaw_pi
    (fun i ↦ (bessel_scaled_increment_law T r t hT hr hrt ht).comp
      (measurePreserving_eval_infinitePi (fun _ : Fin 3 ↦ gaussianCoefficientLaw) i).hasLaw)

end SRWTightness
