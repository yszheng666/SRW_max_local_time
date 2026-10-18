import SRWTightness.EuclideanThirdMoment
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory WithLp

namespace SRWTightness

/-- Coordinatewise square integrability passes to the centered Euclidean observation vector. -/
theorem centered_vector_memLp_two {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 μ) :
    MemLp (fun ω ↦ toLp 2 (fun i ↦ U i ω - ∫ z, U i z ∂μ) : Ω → EuclideanSpace ℝ ι) 2 μ := by
  apply MemLp.of_eval_piLp
  intro i
  exact (hU i).sub (memLp_const _)

/-- The centered Euclidean observation vector has exactly zero Bochner mean. -/
theorem centered_vector_mean_zero {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ι → Ω → ℝ)
    (hU : ∀ i, Integrable (U i) μ) :
    (∫ ω, (toLp 2 (fun i ↦ U i ω - ∫ z, U i z ∂μ) : EuclideanSpace ℝ ι) ∂μ) = 0 := by
  have hi (i : ι) : Integrable (fun ω ↦ U i ω - ∫ z, U i z ∂μ) μ :=
    (hU i).sub (integrable_const _)
  ext i
  rw [eval_integral_piLp hi i]
  change (∫ ω, U i ω - ∫ z, U i z ∂μ ∂μ) = 0
  rw [integral_sub (hU i) (integrable_const _)]
  simp

/-- Every fixed linear transformation and scalar multiple preserves zero centered mean. -/
theorem centered_linear_vector_mean_zero {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ι → Ω → ℝ)
    (hU : ∀ i, Integrable (U i) μ)
    (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (c : ℝ) :
    Integrable (fun ω ↦ c • T (toLp 2 (fun i ↦ U i ω - ∫ z, U i z ∂μ))) μ ∧
      (∫ ω, c • T (toLp 2 (fun i ↦ U i ω - ∫ z, U i z ∂μ)) ∂μ) = 0 := by
  let V : Ω → EuclideanSpace ℝ ι := fun ω ↦ toLp 2 (fun i ↦ U i ω - ∫ z, U i z ∂μ)
  have hV : Integrable V μ := Integrable.of_eval_piLp
    (fun i ↦ (hU i).sub (integrable_const _))
  refine ⟨(c • T).integrable_comp hV, ?_⟩
  change (∫ ω, (c • T) (V ω) ∂μ) = 0
  rw [(c • T).integral_comp_comm hV]
  have hz : (∫ ω, V ω ∂μ) = 0 := centered_vector_mean_zero μ U hU
  rw [hz, map_zero]

end SRWTightness
