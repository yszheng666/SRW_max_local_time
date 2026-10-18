import SRWTightness.KilledFuturePathEvent
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The endpoint of a surviving measurable Brownian path has the exact killed transition law. -/
theorem killed_future_path_law (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    ((gaussianCoefficientLaw.map (fun ω (u : Set.Icc (0 : ℝ) T) ↦
      Real.sqrt T * gaussianDyadicPath ω (u / T))).restrict (dyadicFlatPathEvent T x)).map
        (fun p ↦ x - p ⟨T, hT.le, le_rfl⟩) = killedBrownianDensityLaw T x := by
  letI := killed_brownian_density_law_finite T x hT hx
  have hm : Measurable (fun p : Set.Icc (0 : ℝ) T → ℝ ↦ x - p ⟨T, hT.le, le_rfl⟩) :=
    measurable_const.sub (measurable_pi_apply _)
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hm hA, Measure.restrict_apply (hA.preimage hm)]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact killed_future_path_section hReflection T x hT hx A hA

/-- Endpoint integrals on surviving future paths are integrals of the killed law. -/
theorem killed_future_path_integral (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ p in dyadicFlatPathEvent T x, f (x - p ⟨T, hT.le, le_rfl⟩)
      ∂gaussianCoefficientLaw.map (fun ω (u : Set.Icc (0 : ℝ) T) ↦
        Real.sqrt T * gaussianDyadicPath ω (u / T))) =
      ∫ z, f z ∂killedBrownianDensityLaw T x := by
  rw [← killed_future_path_law hReflection T x hT hx]
  exact (integral_map
    (measurable_const.sub (measurable_pi_apply _)).aemeasurable
    hf.aestronglyMeasurable).symm

end SRWTightness
