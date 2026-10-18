import SRWTightness.ConditionalMomentWindow

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Convert a conditional moment into the event integral needed for endpoint integration. -/
theorem conditional_moment_event_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Set Ω) (f : Ω → ℝ)
    (hpos : 0 < μ.real s) (hf : Integrable f (ProbabilityTheory.cond μ s)) (C : ℝ)
    (hC : (∫ ω, f ω ∂ProbabilityTheory.cond μ s) ≤ C) :
    Integrable f (μ.restrict s) ∧ (∫ ω in s, f ω ∂μ) ≤ C * μ.real s := by
  have hs0 : μ s ≠ 0 := by
    intro h
    simp [Measure.real, h] at hpos
  have hi : Integrable f (μ.restrict s) :=
    (integrable_smul_measure (ENNReal.inv_ne_zero.mpr (measure_ne_top μ s))
      (ENNReal.inv_ne_top.mpr hs0)).mp hf
  refine ⟨hi, ?_⟩
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv] at hC
  change (μ.real s)⁻¹ * (∫ ω in s, f ω ∂μ) ≤ C at hC
  have hh := mul_le_mul_of_nonneg_left hC hpos.le
  calc
    _ = μ.real s * ((μ.real s)⁻¹ * (∫ ω in s, f ω ∂μ)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    _ ≤ μ.real s * C := hh
    _ = _ := mul_comm _ _

end SRWTightness
