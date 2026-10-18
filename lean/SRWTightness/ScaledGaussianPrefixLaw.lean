import SRWTightness.ScaledGaussianPathLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Restricting the actual scaled Brownian path has the exact shorter-duration Brownian law. -/
theorem scaled_gaussian_prefix_law (T r : ℝ) (hT : 0 < T) (hr : 0 < r) (hrT : r ≤ T) :
    gaussianCoefficientLaw.map
      (fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) =
    gaussianCoefficientLaw.map
      (fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt r * gaussianDyadicPath ω (u / r)) := by
  let j : Set.Icc (0 : ℝ) r → Set.Icc (0 : ℝ) T :=
    fun u ↦ ⟨u, u.property.1, u.property.2.trans hrT⟩
  have hP := (scaled_gaussian_path_process T hT).comp_right j
  have hm (S : ℝ) (hS : 0 < S) (u : ℝ) (hu : 0 ≤ u) (huS : u ≤ S) :
      (∫ ω, Real.sqrt S * gaussianDyadicPath ω (u / S) ∂gaussianCoefficientLaw) = 0 := by
    rw [integral_const_mul,
      (gaussianPath_eval_hasLaw (u / S) (div_nonneg hu hS.le)
        ((div_le_one hS).mpr huS)).integral_eq, integral_id_gaussianReal, mul_zero]
  apply gaussian_cross_space_process_law_eq gaussianCoefficientLaw gaussianCoefficientLaw _ _
    hP (scaled_gaussian_path_process r hr)
    (measurable_pi_lambda _ (fun _ ↦
      measurable_const.mul (gaussianDyadicPath_measurable _)))
    (measurable_pi_lambda _ (fun _ ↦
      measurable_const.mul (gaussianDyadicPath_measurable _)))
  · intro u
    exact (hm T hT u u.property.1 (u.property.2.trans hrT)).trans
      (hm r hr u u.property.1 u.property.2).symm
  · intro u v
    change cov[fun ω ↦ Real.sqrt T * gaussianDyadicPath ω (u / T),
      fun ω ↦ Real.sqrt T * gaussianDyadicPath ω (v / T); gaussianCoefficientLaw] = _
    rw [scaled_gaussian_path_covariance T u v hT u.property.1 (u.property.2.trans hrT)
      v.property.1 (v.property.2.trans hrT),
      scaled_gaussian_path_covariance r u v hr u.property.1 u.property.2
        v.property.1 v.property.2]

end SRWTightness
