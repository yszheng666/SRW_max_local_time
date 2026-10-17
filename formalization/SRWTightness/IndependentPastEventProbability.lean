import SRWTightness.IndependentParameterIntegral

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- An independent future event is integrated by its section probability on any past event. -/
theorem independent_past_event_probability {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    (hlY : HasLaw Y ν μ) (hind : IndepFun X Y μ)
    (A : Set α) (hA : MeasurableSet A) (E : Set (α × β)) (hE : MeasurableSet E) :
    μ.real {ω | X ω ∈ A ∧ (X ω, Y ω) ∈ E} =
      ∫ ω in X ⁻¹' A, ν.real (Prod.mk (X ω) ⁻¹' E) ∂μ := by
  classical
  let P : Ω → α × β := fun ω ↦ (X ω, Y ω)
  let F : α × β → ℝ := E.indicator (fun _ ↦ 1)
  have hP : Measurable P := hX.prodMk hY
  have hF : Measurable F := measurable_const.indicator hE
  have hc (ω : Ω) : F (X ω, Y ω) = (P ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) ω := by
    by_cases h : P ω ∈ E <;> simp [F, P, Set.indicator, h] at *
  have hi : Integrable (fun ω ↦ F (X ω, Y ω)) μ := by
    simp_rw [hc]
    exact (integrable_const (1 : ℝ)).indicator (hE.preimage hP)
  have hs (a : α) : (∫ y, F (a, y) ∂ν) = ν.real (Prod.mk a ⁻¹' E) := by
    have hh (y : β) : F (a, y) = (Prod.mk a ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y := by
      by_cases h : (a, y) ∈ E <;> simp [F, Set.indicator, h]
    simp_rw [hh]
    exact integral_indicator_one (hE.preimage (measurable_const.prodMk measurable_id))
  have he := independent_parameter_setIntegral μ ν X Y hX hY hlY hind F hF hi A hA
  simp_rw [hs] at he
  rw [← he]
  simp_rw [hc]
  rw [setIntegral_indicator (hE.preimage hP), setIntegral_const, smul_eq_mul, mul_one]
  rfl

end SRWTightness
