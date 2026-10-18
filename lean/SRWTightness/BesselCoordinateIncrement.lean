import SRWTightness.ExternalBesselThree
import SRWTightness.GaussianUnitIncrementMoment

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Each actual scaled Brownian coordinate has the exact elapsed-time second moment. -/
theorem bessel_coordinate_increment_second_moment (T r s : ℝ) (i : Fin 3)
    (hT : 0 < T) (hr : 0 ≤ r) (hrs : r ≤ s) (hsT : s ≤ T) :
    Integrable (fun ω : Fin 3 → GaussianCoefficientSpace ↦
      (Real.sqrt T * (gaussianDyadicPath (ω i) (s / T) -
        gaussianDyadicPath (ω i) (r / T))) ^ 2) (independentBridgeLaw (Fin 3)) ∧
    (∫ ω : Fin 3 → GaussianCoefficientSpace,
      (Real.sqrt T * (gaussianDyadicPath (ω i) (s / T) -
        gaussianDyadicPath (ω i) (r / T))) ^ 2 ∂independentBridgeLaw (Fin 3)) = s - r := by
  have hr0 := div_nonneg hr hT.le
  have hrs' := (div_le_div_iff_of_pos_right hT).mpr hrs
  have hs1 := (div_le_one hT).mpr hsT
  have hh := gaussian_unit_increment_second_moment (r / T) (s / T) hr0 hrs' hs1
  let f := fun ω : GaussianCoefficientSpace ↦
    (gaussianDyadicPath ω (s / T) - gaussianDyadicPath ω (r / T)) ^ 2
  have hf : Measurable f :=
    ((gaussianDyadicPath_measurable _).sub (gaussianDyadicPath_measurable _)).pow_const 2
  have he : (fun ω : Fin 3 → GaussianCoefficientSpace ↦
      (Real.sqrt T * (gaussianDyadicPath (ω i) (s / T) -
        gaussianDyadicPath (ω i) (r / T))) ^ 2) = (fun ω ↦ T * f (ω i)) := by
    funext ω
    simp only [mul_pow, Real.sq_sqrt hT.le, f]
  rw [he]
  have hp := measurePreserving_eval_infinitePi (fun _ : Fin 3 ↦ gaussianCoefficientLaw) i
  refine ⟨(hp.integrable_comp_of_integrable hh.1).const_mul T, ?_⟩
  rw [integral_const_mul]
  have hm : (independentBridgeLaw (Fin 3)).map (fun ω ↦ ω i) = gaussianCoefficientLaw :=
    Measure.infinitePi_map_eval _ i
  have hg := integral_map (μ := independentBridgeLaw (Fin 3)) (φ := fun ω ↦ ω i)
    (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable
  rw [hm] at hg
  rw [← hg, hh.2]
  field_simp

end SRWTightness
