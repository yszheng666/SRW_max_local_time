import SRWTightness.GaussianQuadraticLaplace
import SRWTightness.BesselCoordinateNegativeMoment

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual radial process has the exact dimension-three quadratic Laplace transform. -/
theorem bessel_three_quadratic_laplace (T x s t : ℝ)
    (hT : 0 < T) (hs : 0 < s) (hsT : s ≤ T) (ht : 0 ≤ t) :
    (∫ ω, Real.exp (-t * (actualBesselThree T x s ω) ^ 2)
      ∂independentBridgeLaw (Fin 3)) =
        Real.exp (-t * x ^ 2 / (1 + 2 * s * t)) /
          (Real.sqrt (1 + 2 * s * t)) ^ 3 := by
  let c : Fin 3 → ℝ := fun i ↦ if i = 0 then x else 0
  let f := fun (i : Fin 3) (ω : GaussianCoefficientSpace) ↦
    Real.exp (-t * (c i + Real.sqrt T * gaussianDyadicPath ω (s / T)) ^ 2)
  have hm (i : Fin 3) : Measurable (f i) := by
    exact (measurable_const.mul ((measurable_const.add
      (measurable_const.mul (gaussianDyadicPath_measurable _))).pow_const 2)).exp
  have hind : iIndepFun (fun (i : Fin 3) (ω : Fin 3 → GaussianCoefficientSpace) ↦ ω i)
      (independentBridgeLaw (Fin 3)) := iIndepFun_infinitePi (fun _ ↦ measurable_id)
  have hi := hind.comp f hm
  have hp := hi.integral_fun_prod_eq_prod_integral
    (fun i ↦ ((hm i).comp (measurable_pi_apply i)).aestronglyMeasurable)
  have he (i : Fin 3) :
      (∫ ω : Fin 3 → GaussianCoefficientSpace, f i (ω i)
        ∂independentBridgeLaw (Fin 3)) =
        Real.exp (-t * (c i) ^ 2 / (1 + 2 * s * t)) /
          Real.sqrt (1 + 2 * s * t) := by
    have hl := gaussianReal_const_add (bessel_scaled_coordinate_law T s i hT hs hsT) (c i)
    simp only [zero_add] at hl
    have hg : Measurable (fun z : ℝ ↦ Real.exp (-t * z ^ 2)) := by fun_prop
    exact (hl.integral_comp hg.aestronglyMeasurable).trans
      (gaussian_quadratic_laplace_integral (c i) s t hs ht)
  have hfun (ω : Fin 3 → GaussianCoefficientSpace) :
      Real.exp (-t * (actualBesselThree T x s ω) ^ 2) = ∏ i, f i (ω i) := by
    rw [actualBesselThree, Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)),
      Finset.mul_sum, Real.exp_sum]
  simp_rw [hfun]
  simp only [Function.comp_def] at hp
  rw [hp]
  simp_rw [he]
  simp [Fin.prod_univ_succ, c] <;> ring

end SRWTightness
