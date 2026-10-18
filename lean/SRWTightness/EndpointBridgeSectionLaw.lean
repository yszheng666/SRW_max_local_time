import SRWTightness.EndpointBridgeProductEvent
import SRWTightness.SourceBridgeConditionalIncrement

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The measurable section and continuous bridge event agree almost everywhere. -/
theorem endpointBridgeProductEvent_section_ae (T l u q d γ b : ℝ)
    (hγ : 0 ≤ γ) (hb : b ∈ Set.Icc l u) :
    (Prod.mk b ⁻¹' endpointBridgeProductEvent T l u q d γ) =ᵐ[gaussianCoefficientLaw]
      bridgeCurvedEvent T b q d γ := by
  filter_upwards [actualIntervalBridge_continuous T] with ω hω
  apply propext
  change (b ∈ Set.Icc l u ∧ ∀ n j : ℕ, (j : ℝ) / 2 ^ n ≤ T →
    endpointBrownianBridge T b ((j : ℝ) / 2 ^ n) ω ≤ q - (d - (j : ℝ) / 2 ^ n) ^ γ) ↔ _
  rw [and_iff_right hb]
  have hc : Continuous (fun v ↦ endpointBrownianBridge T b v ω) :=
    hω.add ((continuous_id.div_const T).mul continuous_const)
  have hbound : Continuous (fun v : ℝ ↦ q - (d - v) ^ γ) :=
    continuous_const.sub ((Real.continuous_rpow_const hγ).comp
      (continuous_const.sub continuous_id))
  have hh := (continuous_barrier_iff_dyadic _ _ hc hbound T).symm
  change _ ↔ ∀ v ∈ Set.Icc (0 : ℝ) T,
    endpointBrownianBridge T b v ω ≤ q - (d - v) ^ γ
  simpa only [Set.mem_Icc, and_imp] using hh

/-- The exact conditional law transfers bridge moments to the measurable product section. -/
theorem endpointBridgeProductEvent_section_cond (T l u q d γ b : ℝ)
    (hγ : 0 ≤ γ) (hb : b ∈ Set.Icc l u) :
    ProbabilityTheory.cond gaussianCoefficientLaw
      (Prod.mk b ⁻¹' endpointBridgeProductEvent T l u q d γ) =
    ProbabilityTheory.cond gaussianCoefficientLaw (bridgeCurvedEvent T b q d γ) := by
  have he := endpointBridgeProductEvent_section_ae T l u q d γ b hγ hb
  unfold ProbabilityTheory.cond
  rw [measure_congr he, Measure.restrict_congr_set he]

end SRWTightness
