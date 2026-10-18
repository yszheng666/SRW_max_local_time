import SRWTightness.IntervalBridgeReversalLaw
import SRWTightness.PositiveBridgeCrossingEvent

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Prescribed endpoint bridge paths are almost surely continuous. -/
theorem positiveEndpointBridge_path_continuous (T x y : ℝ) :
    ∀ᵐ ω ∂gaussianCoefficientLaw, Continuous (fun t : ℝ ↦ positiveEndpointBridge T x y t ω) := by
  filter_upwards [actualIntervalBridge_continuous T] with ω hω
  exact continuous_const.sub (hω.add ((continuous_id.div_const T).mul_const (x - y)))

/-- Reversing an unconditioned endpoint bridge exchanges its two endpoints. -/
theorem positiveEndpointBridge_reversed_path_law (T x y : ℝ) (hT : 0 < T) :
    gaussianCoefficientLaw.map
      (fun ω (t : Set.Icc (0 : ℝ) T) ↦ positiveEndpointBridge T x y (T - t) ω) =
    gaussianCoefficientLaw.map
      (fun ω (t : Set.Icc (0 : ℝ) T) ↦ positiveEndpointBridge T y x t ω) := by
  let H : (Set.Icc (0 : ℝ) T → ℝ) → Set.Icc (0 : ℝ) T → ℝ :=
    fun f t ↦ y - (f t + (t : ℝ) / T * (y - x))
  have hH : Measurable H := by
    apply measurable_pi_lambda
    intro t
    exact measurable_const.sub ((measurable_pi_apply t).add measurable_const)
  have hh := congrArg (fun ν : Measure (Set.Icc (0 : ℝ) T → ℝ) ↦ ν.map H)
    (actualIntervalBridge_reversed_path_law T hT)
  rw [Measure.map_map hH (measurable_pi_lambda _
      (fun t ↦ actualIntervalBridge_measurable T (T - t))),
    Measure.map_map hH (measurable_pi_lambda _
      (fun t ↦ actualIntervalBridge_measurable T t))] at hh
  have he : H ∘ (fun ω (t : Set.Icc (0 : ℝ) T) ↦ actualIntervalBridge T (T - t) ω) =
      (fun ω (t : Set.Icc (0 : ℝ) T) ↦ positiveEndpointBridge T x y (T - t) ω) := by
    funext ω t
    dsimp [H, positiveEndpointBridge, endpointBrownianBridge]
    field_simp
    ring
  rw [he] at hh
  exact hh

end SRWTightness
