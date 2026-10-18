import SRWTightness.BesselCoordinateNegativeMoment
import SRWTightness.RadialInverseProductBound

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- One fixed finite constant for the radial inverse-moment estimate. -/
noncomputable def besselInverseMomentConstant : ℝ :=
  (∫ z : ℝ, |z| ^ (-(1 / 2 : ℝ)) ∂gaussianReal 0 1) ^ 2 + 1

/-- The original inverse-moment input holds uniformly for the actual radial process. -/
theorem bessel_three_inverse_moment_input_internal :
    BesselThreeInverseMomentInput besselInverseMomentConstant := by
  refine ⟨by unfold besselInverseMomentConstant; positivity, ?_⟩
  intro T x s hT hx hs hsT
  let f := fun (i : Fin 3) (ω : Fin 3 → GaussianCoefficientSpace) ↦
    |Real.sqrt T * gaussianDyadicPath (ω i) (s / T)| ^ (-(1 / 2 : ℝ))
  have hp := bessel_two_coordinate_inverse_half_product T s hT hs hsT
  have hn (i : Fin 3) : ∀ᵐ ω ∂independentBridgeLaw (Fin 3),
      Real.sqrt T * gaussianDyadicPath (ω i) (s / T) ≠ 0 := by
    letI : NullSingletonClass (gaussianReal 0 s.toNNReal) :=
      nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hs))
    have hh : ∀ᵐ z ∂gaussianReal 0 s.toNNReal, z ≠ 0 := by simp [ae_iff]
    exact ((bessel_scaled_coordinate_law T s i hT hs hsT).measurePreserving
      (measurable_const.mul ((gaussianDyadicPath_measurable _).comp
        (measurable_pi_apply i)))).quasiMeasurePreserving.ae hh
  have hbound : ∀ᵐ ω ∂independentBridgeLaw (Fin 3),
      (actualBesselThree T x s ω)⁻¹ ≤ f 1 ω * f 2 ω := by
    filter_upwards [hn 1, hn 2] with ω h1 h2
    have hh := radial_inverse_product_bound
      (x + Real.sqrt T * gaussianDyadicPath (ω 0) (s / T))
      (Real.sqrt T * gaussianDyadicPath (ω 1) (s / T))
      (Real.sqrt T * gaussianDyadicPath (ω 2) (s / T)) h1 h2
    simpa [actualBesselThree, Fin.sum_univ_succ, f, add_assoc] using hh
  have hm : Measurable (fun ω ↦ (actualBesselThree T x s ω)⁻¹) := by
    apply Measurable.inv
    unfold actualBesselThree
    apply Measurable.sqrt
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_const.add (measurable_const.mul
      ((gaussianDyadicPath_measurable _).comp (measurable_pi_apply i)))).pow_const 2
  have hi : Integrable (fun ω ↦ (actualBesselThree T x s ω)⁻¹)
      (independentBridgeLaw (Fin 3)) := by
    apply hp.1.mono' hm.aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    have hr : 0 ≤ actualBesselThree T x s ω := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr)]
    exact hω
  refine ⟨hi, ?_⟩
  have hh := integral_mono_ae hi hp.1 hbound
  rw [hp.2] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg s)
  unfold besselInverseMomentConstant
  linarith

end SRWTightness
