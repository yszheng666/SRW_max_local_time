import SRWTightness.InverseTiltEvent
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A tilt on the first coordinate leaves an independent auxiliary law unchanged. -/
theorem tilted_prod_left {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (hX : Integrable (fun ω ↦ Real.exp (X ω)) μ) :
    (μ.tilted X).prod ν = (μ.prod ν).tilted (fun ω ↦ X ω.1) := by
  have hm : AEMeasurable
      (fun ω ↦ ENNReal.ofReal (Real.exp (X ω) / ∫ x, Real.exp (X x) ∂μ)) μ :=
    (hX.aestronglyMeasurable.aemeasurable.div_const _).ennreal_ofReal
  rw [Measure.tilted, prod_withDensity_left₀ hm, Measure.tilted]
  have hi : (∫ ω : Ω × Ξ, Real.exp (X ω.1) ∂μ.prod ν) =
      ∫ ω, Real.exp (X ω) ∂μ := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := μ) (ν := ν) (fun ω ↦ Real.exp (X ω)))
  rw [hi]

/-- The first-coordinate cumulant is unchanged by adjoining independent probability variables. -/
theorem cgf_prod_fst {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (s : ℝ) : cgf (fun ω ↦ X ω.1) (μ.prod ν) s = cgf X μ s := by
  unfold cgf mgf
  have hi := integral_fun_fst (μ := μ) (ν := ν) (fun ω ↦ Real.exp (s * X ω))
  simp only [probReal_univ, one_smul] at hi
  exact congrArg Real.log hi

/-- Inverse-tilt event bounds also cover events using independent auxiliary paths. -/
theorem inverse_tilt_product_event_bounds {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (hX : Integrable (fun ω ↦ Real.exp (X ω)) μ)
    (E : Set (Ω × Ξ)) (hE : MeasurableSet E) (L U : ℝ)
    (hL : ∀ ω ∈ E, L ≤ Real.exp (cgf X μ 1 - X ω.1))
    (hU : ∀ ω ∈ E, Real.exp (cgf X μ 1 - X ω.1) ≤ U) :
    L * ((μ.tilted X).prod ν).real E ≤ (μ.prod ν).real E ∧
      (μ.prod ν).real E ≤ U * ((μ.tilted X).prod ν).real E := by
  have hi : Integrable (fun ω : Ω × Ξ ↦ Real.exp (X ω.1)) (μ.prod ν) :=
    ((memLp_one_iff_integrable.mpr hX).comp_fst ν).integrable le_rfl
  have hh := inverse_tilt_event_bounds (μ.prod ν) (fun ω ↦ X ω.1) hi E hE L U
    (by simpa only [cgf_prod_fst] using hL) (by simpa only [cgf_prod_fst] using hU)
  rwa [← tilted_prod_left μ ν X hX] at hh

end SRWTightness
