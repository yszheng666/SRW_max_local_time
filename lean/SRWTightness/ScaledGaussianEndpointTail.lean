import SRWTightness.BesselIncrementLaw
import SRWTightness.AtomlessTailContinuity

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The terminal value of the scaled actual Brownian path has its exact Gaussian law. -/
theorem scaled_gaussian_endpoint_hasLaw (T : ℝ) (hT : 0 < T) :
    HasLaw (fun ω ↦ Real.sqrt T * gaussianDyadicPath ω (T / T))
      (gaussianReal 0 T.toNNReal) gaussianCoefficientLaw := by
  simpa only [zero_div, gaussianDyadicPath_zero, sub_zero] using
    bessel_scaled_increment_law T 0 T hT le_rfl hT.le le_rfl

/-- Every closed terminal tail of the actual scaled Brownian path is the Gaussian tail. -/
theorem scaled_gaussian_endpoint_tail (T c : ℝ) (hT : 0 < T) :
    gaussianCoefficientLaw.real {ω | c ≤ Real.sqrt T * gaussianDyadicPath ω (T / T)} =
      (gaussianReal 0 T.toNNReal).real (Set.Ici c) := by
  have he := congrArg (fun μ : Measure ℝ ↦ μ.real (Set.Ici c))
    (scaled_gaussian_endpoint_hasLaw T hT).map_eq
  have hm : Measurable (fun ω ↦ Real.sqrt T * gaussianDyadicPath ω (T / T)) :=
    measurable_const.mul (gaussianDyadicPath_measurable _)
  rw [map_measureReal_apply hm measurableSet_Ici] at he
  exact he

/-- The scaled actual Brownian terminal tail varies continuously with its threshold. -/
theorem scaled_gaussian_endpoint_tail_continuous (T : ℝ) (hT : 0 < T) :
    Continuous (fun c ↦ gaussianCoefficientLaw.real
      {ω | c ≤ Real.sqrt T * gaussianDyadicPath ω (T / T)}) := by
  have hv : T.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hT)
  letI := nullSingletonClass_gaussianReal (μ := 0) hv
  simp_rw [scaled_gaussian_endpoint_tail T _ hT]
  exact continuous_iff_continuousAt.mpr (fun c ↦
    measure_real_tail_continuousAt (gaussianReal 0 T.toNNReal) c (measure_singleton c))

end SRWTightness
