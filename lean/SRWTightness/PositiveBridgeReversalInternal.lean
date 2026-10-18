import SRWTightness.PositiveBridgeUnconditionedReversal
import SRWTightness.ConditionalContinuousPathLaw

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The flat-barrier coefficient event is exactly nonnegativity of its endpoint bridge. -/
theorem bridgeFlatEvent_eq_positivePath (T x y : ℝ) :
    bridgeFlatEvent T (x - y) x =
      {ω | ∀ t : Set.Icc (0 : ℝ) T, 0 ≤ positiveEndpointBridge T x y t ω} := by
  ext ω
  constructor
  · intro h t
    exact sub_nonneg.mpr (h t t.property)
  · intro h t ht
    exact sub_nonneg.mp (h ⟨t, ht⟩)

/-- The same coefficient event is nonnegativity of the entire reversed path. -/
theorem bridgeFlatEvent_eq_reversed_positivePath (T x y : ℝ) :
    bridgeFlatEvent T (x - y) x =
      {ω | ∀ t : Set.Icc (0 : ℝ) T, 0 ≤ positiveEndpointBridge T x y (T - t) ω} := by
  rw [bridgeFlatEvent_eq_positivePath]
  ext ω
  constructor
  · intro h t
    exact h ⟨T - t, by constructor <;> linarith [t.property.1, t.property.2]⟩
  · intro h t
    have ht : T - (t : ℝ) ∈ Set.Icc (0 : ℝ) T :=
      ⟨by linarith [t.property.2], by linarith [t.property.1]⟩
    simpa only [sub_sub_cancel] using h ⟨T - t, ht⟩

/-- The original positive bridge reversal input holds for its actual conditioned path law. -/
theorem positive_bridge_reversal_input_internal : PositiveBridgeReversalInput := by
  intro T x y hT hx hy
  letI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  unfold positiveBridgeCoefficientLaw
  rw [bridgeFlatEvent_eq_reversed_positivePath, bridgeFlatEvent_eq_positivePath]
  apply continuous_path_nonnegative_conditional_law_eq
  · apply measurable_pi_lambda
    intro t
    exact measurable_const.sub
      ((actualIntervalBridge_measurable T (T - t)).add measurable_const)
  · exact positiveEndpointBridge_path_measurable T y x T
  · filter_upwards [positiveEndpointBridge_path_continuous T x y] with ω hω
    exact hω.comp (continuous_const.sub continuous_subtype_val)
  · filter_upwards [positiveEndpointBridge_path_continuous T y x] with ω hω
    exact hω.comp continuous_subtype_val
  · exact positiveEndpointBridge_reversed_path_law T x y hT

end SRWTightness
