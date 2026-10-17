import SRWTightness.PositiveBridgeCrossingEvent

open MeasureTheory ProbabilityTheory

namespace SRWTightness

instance positiveBridgeCoefficientLaw_zeroOrProbability (T x y : ℝ) :
    IsZeroOrProbabilityMeasure (positiveBridgeCoefficientLaw T x y) := by
  unfold positiveBridgeCoefficientLaw
  infer_instance

/-- Restrict the full standard reversal identity to any initial subinterval. -/
theorem positiveBridge_reversal_restrict (hReverse : PositiveBridgeReversalInput)
    (T x y s : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) (hsT : s ≤ T) :
    (positiveBridgeCoefficientLaw T x y).map
      (fun ω (t : Set.Icc (0 : ℝ) s) ↦ positiveEndpointBridge T x y (T - t) ω) =
    (positiveBridgeCoefficientLaw T y x).map
      (fun ω (t : Set.Icc (0 : ℝ) s) ↦ positiveEndpointBridge T y x t ω) := by
  let restrictPath : (Set.Icc (0 : ℝ) T → ℝ) → (Set.Icc (0 : ℝ) s → ℝ) :=
    fun f t ↦ f ⟨t, t.property.1, t.property.2.trans hsT⟩
  have hr : Measurable restrictPath := measurable_pi_iff.mpr
    (fun t ↦ measurable_pi_apply _)
  have hl : Measurable (fun ω (t : Set.Icc (0 : ℝ) T) ↦
      positiveEndpointBridge T x y (T - t) ω) :=
    measurable_pi_iff.mpr (fun t ↦ positiveEndpointBridge_measurable T x y _)
  have h := congrArg (fun μ ↦ μ.map restrictPath) (hReverse T x y hT hx hy)
  rw [Measure.map_map hr hl,
    Measure.map_map hr (positiveEndpointBridge_path_measurable T y x T)] at h
  exact h

/-- Full-time strict crossing events can be reversed using their countable measurable versions. -/
theorem positiveBridge_reversed_crossing (hReverse : PositiveBridgeReversalInput)
    (T x y s : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) (hsT : s ≤ T)
    (bound : ℝ → ℝ) (hb : Continuous bound) :
    (positiveBridgeCoefficientLaw T x y).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) s, positiveEndpointBridge T x y (T - t) ω < bound t} =
    (positiveBridgeCoefficientLaw T y x).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) s, positiveEndpointBridge T y x t ω < bound t} := by
  have hm : Measurable (fun ω (t : Set.Icc (0 : ℝ) s) ↦
      positiveEndpointBridge T x y (T - t) ω) :=
    measurable_pi_iff.mpr (fun t ↦ positiveEndpointBridge_measurable T x y _)
  calc
    _ = ((positiveBridgeCoefficientLaw T x y).map
        (fun ω (t : Set.Icc (0 : ℝ) s) ↦ positiveEndpointBridge T x y (T - t) ω)).real
          (dyadicLowerPathEvent s bound) := by
      rw [map_measureReal_apply hm (dyadicLowerPathEvent_measurable s bound)]
      apply measureReal_congr
      filter_upwards [positiveEndpointBridge_ae_continuous T x y] with ω hω
      exact propext (continuous_crossing_iff_dyadic _ bound
        (hω.comp (continuous_const.sub continuous_id)) hb s)
    _ = ((positiveBridgeCoefficientLaw T y x).map
        (fun ω (t : Set.Icc (0 : ℝ) s) ↦ positiveEndpointBridge T y x t ω)).real
          (dyadicLowerPathEvent s bound) := by
      rw [positiveBridge_reversal_restrict hReverse T x y s hT hx hy hsT]
    _ = _ := (positiveBridge_crossing_real T y x s bound hb).symm

end SRWTightness
