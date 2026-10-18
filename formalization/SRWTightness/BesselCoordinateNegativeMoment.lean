import SRWTightness.GaussianInverseHalfScaling
import SRWTightness.ExternalBesselThree
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

/-- Each unshifted coordinate in the actual radial construction has its exact Gaussian law. -/
theorem bessel_scaled_coordinate_law (T s : ℝ) (i : Fin 3)
    (hT : 0 < T) (hs : 0 < s) (hsT : s ≤ T) :
    HasLaw (fun ω : Fin 3 → GaussianCoefficientSpace ↦
      Real.sqrt T * gaussianDyadicPath (ω i) (s / T))
      (gaussianReal 0 s.toNNReal) (independentBridgeLaw (Fin 3)) := by
  have hu : HasLaw (fun ω : Fin 3 → GaussianCoefficientSpace ↦
      gaussianDyadicPath (ω i) (s / T)) (gaussianReal 0 (s / T).toNNReal)
      (independentBridgeLaw (Fin 3)) :=
    HasLaw.comp (gaussianPath_eval_hasLaw (s / T) (div_pos hs hT).le
      ((div_le_one hT).mpr hsT))
      (measurePreserving_eval_infinitePi (fun _ : Fin 3 ↦ gaussianCoefficientLaw) i).hasLaw
  have hv : NNReal.mk ((Real.sqrt T) ^ 2) (sq_nonneg _) * (s / T).toNNReal =
      s.toNNReal := by
    apply Subtype.ext
    change (Real.sqrt T) ^ 2 * max (s / T) 0 = max s 0
    rw [Real.sq_sqrt hT.le, max_eq_left (div_pos hs hT).le, max_eq_left hs.le]
    field_simp
  simpa only [mul_zero, hv] using gaussianReal_const_mul hu (Real.sqrt T)

/-- Each actual unshifted coordinate has an integrable inverse-half absolute moment. -/
theorem bessel_coordinate_inverse_half_moment (T s : ℝ) (i : Fin 3)
    (hT : 0 < T) (hs : 0 < s) (hsT : s ≤ T) :
    Integrable (fun ω : Fin 3 → GaussianCoefficientSpace ↦
      |Real.sqrt T * gaussianDyadicPath (ω i) (s / T)| ^ (-(1 / 2 : ℝ)))
      (independentBridgeLaw (Fin 3)) ∧
    (∫ ω : Fin 3 → GaussianCoefficientSpace,
      |Real.sqrt T * gaussianDyadicPath (ω i) (s / T)| ^ (-(1 / 2 : ℝ))
      ∂independentBridgeLaw (Fin 3)) =
      (Real.sqrt s) ^ (-(1 / 2 : ℝ)) *
        (∫ z : ℝ, |z| ^ (-(1 / 2 : ℝ)) ∂gaussianReal 0 1) := by
  have hlaw := bessel_scaled_coordinate_law T s i hT hs hsT
  have hm : Measurable (fun ω : Fin 3 → GaussianCoefficientSpace ↦
      Real.sqrt T * gaussianDyadicPath (ω i) (s / T)) :=
    measurable_const.mul ((gaussianDyadicPath_measurable _).comp (measurable_pi_apply i))
  have hh := gaussian_inverse_half_scaling s hs
  refine ⟨(hlaw.measurePreserving hm).integrable_comp_of_integrable hh.1, ?_⟩
  exact (hlaw.integral_comp hh.1.aestronglyMeasurable).trans hh.2

/-- The two unshifted coordinate factors have an exact finite product moment. -/
theorem bessel_two_coordinate_inverse_half_product (T s : ℝ)
    (hT : 0 < T) (hs : 0 < s) (hsT : s ≤ T) :
    let f := fun (i : Fin 3) (ω : Fin 3 → GaussianCoefficientSpace) ↦
      |Real.sqrt T * gaussianDyadicPath (ω i) (s / T)| ^ (-(1 / 2 : ℝ))
    Integrable (fun ω ↦ f 1 ω * f 2 ω) (independentBridgeLaw (Fin 3)) ∧
    (∫ ω, f 1 ω * f 2 ω ∂independentBridgeLaw (Fin 3)) =
      (∫ z : ℝ, |z| ^ (-(1 / 2 : ℝ)) ∂gaussianReal 0 1) ^ 2 / Real.sqrt s := by
  dsimp only
  have hind : iIndepFun (fun (i : Fin 3) (ω : Fin 3 → GaussianCoefficientSpace) ↦ ω i)
      (independentBridgeLaw (Fin 3)) := iIndepFun_infinitePi (fun _ ↦ measurable_id)
  have hm : Measurable (fun ω : GaussianCoefficientSpace ↦
      |Real.sqrt T * gaussianDyadicPath ω (s / T)| ^ (-(1 / 2 : ℝ))) := by
    exact (measurable_const.mul (gaussianDyadicPath_measurable _)).abs.pow measurable_const
  have hi := (hind.indepFun (show (1 : Fin 3) ≠ 2 by decide)).comp hm hm
  have h1 := bessel_coordinate_inverse_half_moment T s 1 hT hs hsT
  have h2 := bessel_coordinate_inverse_half_moment T s 2 hT hs hsT
  refine ⟨hi.integrable_mul h1.1 h2.1, ?_⟩
  have hh := hi.integral_mul_eq_mul_integral h1.1.aestronglyMeasurable h2.1.aestronglyMeasurable
  simp only [Function.comp_def, Pi.mul_apply] at hh
  rw [h1.2, h2.2] at hh
  rw [hh]
  have hp : (Real.sqrt s) ^ (-(1 / 2 : ℝ)) * (Real.sqrt s) ^ (-(1 / 2 : ℝ)) =
      (Real.sqrt s)⁻¹ := by
    rw [← Real.rpow_add (Real.sqrt_pos.mpr hs)]
    norm_num [Real.rpow_neg_one]
  calc
    _ = ((Real.sqrt s) ^ (-(1 / 2 : ℝ)) * (Real.sqrt s) ^ (-(1 / 2 : ℝ))) *
        (∫ z : ℝ, |z| ^ (-(1 / 2 : ℝ)) ∂gaussianReal 0 1) ^ 2 := by ring
    _ = _ := by rw [hp]; ring

end SRWTightness
