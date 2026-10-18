import Mathlib.Probability.ConditionalProbability

open MeasureTheory
namespace SRWTightness

/-- An almost-sure implication on a measurable fiber becomes an almost-sure fact under its
conditional law. This also covers a zero-mass fiber. -/
theorem ae_cond_of_ae_imp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (H : Set Ω) (hH : MeasurableSet H) (P : Ω → Prop)
    (h : ∀ᵐ x ∂μ, x ∈ H → P x) :
    ∀ᵐ x ∂ProbabilityTheory.cond μ H, P x := by
  filter_upwards [ProbabilityTheory.cond_absolutelyContinuous.ae_le h,
    ProbabilityTheory.ae_cond_mem (μ := μ) hH] with x hx hmem
  exact hx hmem

end SRWTightness
