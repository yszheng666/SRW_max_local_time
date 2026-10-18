import SRWTightness.ExternalPositiveBridge

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- At a deterministic positive unit time, a Brownian coordinate avoids every singleton. -/
theorem gaussian_unit_path_ae_ne (s a : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ ω ∂gaussianCoefficientLaw, gaussianDyadicPath ω s ≠ a := by
  letI : NullSingletonClass (gaussianReal 0 s.toNNReal) :=
    nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hs))
  have hh : ∀ᵐ x ∂gaussianReal 0 s.toNNReal, x ≠ a := by simp [ae_iff]
  exact ((gaussianPath_eval_hasLaw s hs.le hs1).measurePreserving
    (gaussianDyadicPath_measurable s)).quasiMeasurePreserving.ae hh

/-- The entire original deterministic-time positivity input for the actual radial process. -/
theorem bessel_three_positive_input_internal : BesselThreePositiveInput := by
  intro T x s hT hx hs hsT
  have hunit := gaussian_unit_path_ae_ne (s / T) 0 (div_pos hs hT)
    ((div_le_one hT).mpr hsT)
  have hh : ∀ᵐ ω ∂independentBridgeLaw (Fin 3),
      gaussianDyadicPath (ω (1 : Fin 3)) (s / T) ≠ 0 :=
    (measurePreserving_eval_infinitePi (fun _ : Fin 3 ↦ gaussianCoefficientLaw)
      (1 : Fin 3)).quasiMeasurePreserving.ae hunit
  filter_upwards [hh] with ω hω
  unfold actualBesselThree
  apply Real.sqrt_pos.mpr
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ sq_nonneg _)).mpr
  refine ⟨(1 : Fin 3), Finset.mem_univ _, ?_⟩
  simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, zero_add]
  exact sq_pos_of_ne_zero (mul_ne_zero (Real.sqrt_pos.mpr hT).ne' hω)

end SRWTightness
