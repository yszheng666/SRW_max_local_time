import SRWTightness.PositiveBridgeFullCurve
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace SRWTightness

noncomputable def positiveBridgeCurveConstant (C γ M : ℝ) : ℝ :=
  8 * Real.exp M *
    ((2 : ℝ) ^ γ + C * (3 : ℝ) ^ γ / (1 - (2 : ℝ) ^ (γ - 1 / 2)) + 1)

/-- Both halves decay with H alone, uniformly over all positive durations. -/
theorem positiveBridge_failure_single_power (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (C : ℝ) (hMoment : BesselThreeInverseMomentInput C)
    (T x y H γ M : ℝ) (hT : 0 < T) (hH : 0 < H) (hx : Real.sqrt H ≤ x)
    (hy : Real.sqrt (H + T) ≤ y) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (hxy : 2 * x * y / T ≤ 1) (hM : (x - y) ^ 2 / (2 * T) ≤ M) :
    (positiveBridgeCoefficientLaw T x y).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, positiveEndpointBridge T x y t ω < (H + t) ^ γ} ≤
      positiveBridgeCurveConstant C γ M * H ^ (γ - 1 / 2) := by
  have h := positiveBridge_curved_failure_bound hBridge hReverse hPositive hInitial hHit C hMoment
    T x y H γ M hT hH hx hy hγ hγhalf hxy hM
  have hr : (H + T) ^ (γ - 1 / 2) ≤ H ^ (γ - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos hH (by linarith) (by linarith)
  apply h.trans
  calc
    _ ≤ (8 * Real.exp M) *
        ((((2 : ℝ) ^ γ + C * (3 : ℝ) ^ γ / (1 - (2 : ℝ) ^ (γ - 1 / 2))) *
          H ^ (γ - 1 / 2)) + H ^ (γ - 1 / 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hr) (by positivity)
    _ = _ := by unfold positiveBridgeCurveConstant; ring

/-- A fixed negative power can be made smaller than one half at a uniform threshold. -/
theorem curvedBarrier_half_threshold (K γ : ℝ) (hγ : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → K * H ^ (γ - 1 / 2) ≤ 1 / 2 := by
  have hp := tendsto_rpow_neg_atTop (by linarith : 0 < (1 / 2 : ℝ) - γ)
  have he : -((1 / 2 : ℝ) - γ) = γ - 1 / 2 := by ring
  rw [he] at hp
  have hc := hp.const_mul K
  simp only [mul_zero] at hc
  have hev : ∀ᶠ H : ℝ in atTop, K * H ^ (γ - 1 / 2) < 1 / 2 :=
    (tendsto_order.mp hc).2 _ (by norm_num)
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp hev
  refine ⟨max 1 H₀, le_max_left _ _, ?_⟩
  intro H hH
  exact (hH₀ H ((le_max_right _ _).trans hH)).le

/-- The full positive-bridge curved failure probability is at most one half for large H. -/
theorem positiveBridge_failure_half (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (C : ℝ) (hMoment : BesselThreeInverseMomentInput C)
    (γ M : ℝ) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H T x y : ℝ, H₀ ≤ H → 0 < T →
      Real.sqrt H ≤ x → Real.sqrt (H + T) ≤ y →
      2 * x * y / T ≤ 1 → (x - y) ^ 2 / (2 * T) ≤ M →
      (positiveBridgeCoefficientLaw T x y).real
        {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, positiveEndpointBridge T x y t ω < (H + t) ^ γ} ≤
          1 / 2 := by
  obtain ⟨H₀, hH₀, hsmall⟩ := curvedBarrier_half_threshold (positiveBridgeCurveConstant C γ M) γ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro H T x y hH hT hx hy hxy hM
  exact (positiveBridge_failure_single_power hBridge hReverse hPositive hInitial hHit C hMoment
    T x y H γ M hT (by linarith) hx hy hγ hγhalf hxy hM).trans (hsmall H hH)

end SRWTightness
