import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory
namespace SRWTightness

/-- Conditioning only the first coordinate preserves the independent second-coordinate law. -/
theorem conditional_product_left {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [SFinite μ] (σ : Measure Γ) [IsProbabilityMeasure σ] (H : Set Ω) :
    ProbabilityTheory.cond (μ.prod σ) (H ×ˢ Set.univ) =
      (ProbabilityTheory.cond μ H).prod σ := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod, measure_univ, mul_one, Measure.prod_smul_left]
  congr 1
  simpa only [Measure.restrict_univ] using (Measure.prod_restrict (μ := μ) (ν := σ) H Set.univ).symm

/-- A measure-preserving map remains so after conditioning on a measurable target event. -/
theorem conditional_preserving {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {μ : Measure Ω} {ν : Measure Γ} {f : Ω → Γ} (hf : MeasurePreserving f μ ν)
    (H : Set Γ) (hH : MeasurableSet H) :
    MeasurePreserving f (ProbabilityTheory.cond μ (f ⁻¹' H)) (ProbabilityTheory.cond ν H) := by
  unfold ProbabilityTheory.cond
  rw [hf.measure_preimage hH.nullMeasurableSet]
  exact (hf.restrict_preimage hH).smul_measure _

end SRWTightness
