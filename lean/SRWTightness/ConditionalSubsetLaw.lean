import SRWTightness.BridgeConditionalProbability

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A second conditioning on a subevent removes the first conditioning, also for completed events. -/
theorem conditional_subset_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s t : Set Ω)
    (hs : NullMeasurableSet s μ) (hs0 : μ s ≠ 0) (hts : t ⊆ s) :
    ProbabilityTheory.cond (ProbabilityTheory.cond μ s) t = ProbabilityTheory.cond μ t := by
  have he : t ∩ s = t := Set.inter_eq_left.mpr hts
  unfold ProbabilityTheory.cond
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply₀' hs, he,
    Measure.restrict_smul, Measure.restrict_restrict_of_subset hts, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inr (measure_ne_top _ _))
    (Or.inl (ENNReal.inv_ne_top.mpr hs0)), inv_inv]
  calc
    μ s * (μ t)⁻¹ * (μ s)⁻¹ = (μ t)⁻¹ * (μ s * (μ s)⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hs0 (measure_ne_top _ _), mul_one]

end SRWTightness
