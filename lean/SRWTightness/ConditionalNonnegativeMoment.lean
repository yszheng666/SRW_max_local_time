import SRWTightness.BridgeConditionalProbability

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Conditioning on an event of probability at least one half at most doubles a nonnegative moment. -/
theorem conditional_nonnegative_moment_half {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Set Ω) (f : Ω → ℝ)
    (hhalf : 1 / 2 ≤ μ.real s) (hf : Integrable f μ) (hn : ∀ ω, 0 ≤ f ω) :
    Integrable f (ProbabilityTheory.cond μ s) ∧
      (∫ ω, f ω ∂ProbabilityTheory.cond μ s) ≤ 2 * ∫ ω, f ω ∂μ := by
  have hpos : 0 < μ.real s := by linarith
  have hne : μ s ≠ 0 := by
    intro h
    simp [Measure.real, h] at hpos
  have hrestrict := hf.mono_measure (Measure.restrict_le_self (μ := μ) (s := s))
  constructor
  · exact hrestrict.smul_measure (ENNReal.inv_ne_top.mpr hne)
  · rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
    change (μ.real s)⁻¹ * (∫ ω, f ω ∂μ.restrict s) ≤ _
    have hbound : (μ.real s)⁻¹ ≤ 2 := by
      rw [← one_div]
      exact (div_le_iff₀ hpos).mpr (by linarith)
    have hi := integral_mono_measure (Measure.restrict_le_self (μ := μ) (s := s))
      (Filter.Eventually.of_forall hn) hf
    calc
      _ ≤ 2 * (∫ ω, f ω ∂μ.restrict s) :=
        mul_le_mul_of_nonneg_right hbound (integral_nonneg hn)
      _ ≤ _ := mul_le_mul_of_nonneg_left hi (by norm_num)

end SRWTightness
