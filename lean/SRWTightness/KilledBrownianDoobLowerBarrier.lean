import SRWTightness.KilledBrownianDoobEventReal
import SRWTightness.KilledFuturePathLaw
import SRWTightness.KilledBrownianFirstMoment

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Staying above a positive lower level under the Doob law has an exact killed-kernel mass. -/
theorem killed_brownian_doob_lower_barrier (hReflection : BridgeReflectionInput)
    (T x b : ℝ) (hT : 0 < T) (hb : 0 < b) (hbx : b < x) :
    (killedBrownianDoobCoefficientLaw T x).real {ω |
      (fun u : Set.Icc (0 : ℝ) T ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈
        dyadicFlatPathEvent T (x - b)} =
      ((x - b) + b * (killedBrownianDensityLaw T (x - b)).real Set.univ) / x := by
  have hx : 0 < x := hb.trans hbx
  have hq : 0 < x - b := sub_pos.mpr hbx
  letI := killed_brownian_density_law_finite T (x - b) hT hq
  let P := fun ω (u : Set.Icc (0 : ℝ) T) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  let e : Set.Icc (0 : ℝ) T := ⟨T, hT.le, le_rfl⟩
  let E := P ⁻¹' dyadicFlatPathEvent T (x - b)
  let S := {ω | ∀ t ∈ Set.Icc (0 : ℝ) T,
    0 < x - Real.sqrt T * gaussianDyadicPath ω (t / T)}
  have hP : Measurable P := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  have hE : MeasurableSet E := (dyadicFlatPathEvent_measurable T (x - b)).preimage hP
  have he : (S ∩ E : Set GaussianCoefficientSpace) =ᵐ[gaussianCoefficientLaw] E := by
    filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
    apply propext
    change (ω ∈ S ∧ ω ∈ E) ↔ ω ∈ E
    constructor
    · exact And.right
    · intro h
      refine ⟨?_, h⟩
      have hc : Continuous (fun t ↦ Real.sqrt T * gaussianDyadicPath ω (t / T)) :=
        continuous_const.mul (hω.comp (continuous_id.div_const T))
      have hf := (continuous_flat_iff_dyadic _ hc T (x - b)).mpr h
      intro t ht
      have hh := hf t ht
      linarith
  change (killedBrownianDoobCoefficientLaw T x).real E = _
  rw [killed_brownian_doob_event_real hReflection T x hT hx E hE]
  change (∫ ω in S ∩ E, (x - P ω e) / x ∂gaussianCoefficientLaw) = _
  rw [setIntegral_congr_set he, integral_div]
  congr 1
  have hfun (ω) : x - P ω e = ((x - b) - P ω e) + b := by ring
  simp_rw [hfun]
  have hf : Measurable (fun p : Set.Icc (0 : ℝ) T → ℝ ↦ ((x - b) - p e) + b) := by
    fun_prop
  change (∫ ω in P ⁻¹' dyadicFlatPathEvent T (x - b),
    ((x - b) - P ω e) + b ∂gaussianCoefficientLaw) = _
  rw [← setIntegral_map (dyadicFlatPathEvent_measurable T (x - b))
    hf.aestronglyMeasurable hP.aemeasurable]
  rw [killed_future_path_integral hReflection T (x - b) hT hq
    (fun z ↦ z + b) (by fun_prop)]
  rw [integral_add (killed_brownian_endpoint_integrable T (x - b) hT hq)
    (integrable_const b), killed_brownian_first_moment T (x - b) hT hq,
    integral_const, smul_eq_mul, mul_comm]

end SRWTightness
