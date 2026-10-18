import SRWTightness.FiniteConditionalLower

open MeasureTheory
namespace SRWTightness

/-- Conditioning a success event with a count fiber gives exactly the normalized restricted
original measure used by the joint-root aggregation. The success set need not be measurable. -/
theorem conditional_restricted_event_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H C S : Set Ω) (hH : MeasurableSet H) (hC : MeasurableSet C) :
    (ProbabilityTheory.cond μ H).real (S ∩ C) =
      (μ.restrict S).real (H ∩ C) / μ.real H := by
  rw [conditional_real_apply μ H (S ∩ C) hH,
    measureReal_restrict_apply (hH.inter hC)]
  congr 2
  ext x
  simp only [Set.mem_inter_iff]
  tauto

end SRWTightness
