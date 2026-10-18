import SRWTightness.SourceBridgeSurvival

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Reversal transports continuous barrier survival, including its null-set completion. -/
theorem positiveBridge_reversed_survival (hReflection : BridgeReflectionInput)
    (hReverse : PositiveBridgeReversalInput) (T x y s : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) (hsT : s ≤ T)
    (bound : ℝ → ℝ) (hb : Continuous bound) :
    (positiveBridgeCoefficientLaw T x y).real
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) s,
        bound t ≤ positiveEndpointBridge T x y (T - t) ω} =
    (positiveBridgeCoefficientLaw T y x).real
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) s,
        bound t ≤ positiveEndpointBridge T y x t ω} := by
  letI := positiveBridge_probability hReflection T x y hT hx hy
  have hn : NullMeasurableSet
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) s,
        positiveEndpointBridge T x y (T - t) ω < bound t}
      (positiveBridgeCoefficientLaw T x y) := by
    refine ⟨(fun ω (t : Set.Icc (0 : ℝ) s) ↦
        positiveEndpointBridge T x y (T - t) ω) ⁻¹' dyadicLowerPathEvent s bound,
      (dyadicLowerPathEvent_measurable s bound).preimage
        (measurable_pi_iff.mpr (fun t ↦ positiveEndpointBridge_measurable T x y _)), ?_⟩
    filter_upwards [positiveEndpointBridge_ae_continuous T x y] with ω hω
    exact propext (continuous_crossing_iff_dyadic _ bound
      (hω.comp (continuous_const.sub continuous_id)) hb s)
  have he : {ω | ∀ t ∈ Set.Icc (0 : ℝ) s,
      bound t ≤ positiveEndpointBridge T x y (T - t) ω} =
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) s,
        positiveEndpointBridge T x y (T - t) ω < bound t}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_and, not_lt]
  rw [he, probReal_compl_eq_one_sub₀ hn,
    positiveBridge_reversed_crossing hReverse T x y s hT hx hy hsT bound hb,
    positiveBridge_survival_real hReflection T y x s hT hy hx bound hb]

/-- The source curved event under flat conditioning has the reversed positive-bridge law. -/
theorem sourceBridge_curved_conditional_identity (hReflection : BridgeReflectionInput)
    (hReverse : PositiveBridgeReversalInput) (T H q b γ : ℝ)
    (hT : 0 < T) (hq : 0 < q) (hb : b < q) (hγ : 0 ≤ γ) :
    (positiveBridgeCoefficientLaw T q (q - b)).real
      (bridgeCurvedEvent T b q (H + T) γ) =
    (positiveBridgeCoefficientLaw T (q - b) q).real
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T,
        (H + t) ^ γ ≤ positiveEndpointBridge T (q - b) q t ω} := by
  have he : bridgeCurvedEvent T b q (H + T) γ =
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T,
        (H + t) ^ γ ≤ positiveEndpointBridge T q (q - b) (T - t) ω} := by
    ext ω
    rw [bridgeCurvedEvent_reverse]
    simp only [Set.mem_setOf_eq, source_reversed_positiveBridge]
  rw [he]
  exact positiveBridge_reversed_survival hReflection hReverse T q (q - b) T
    hT hq (sub_pos.mpr hb) le_rfl _
    ((Real.continuous_rpow_const hγ).comp (continuous_const.add continuous_id))

end SRWTightness
