import SRWTightness.ActualIntervalBridge
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The existing centered bridge with a prescribed terminal value. -/
noncomputable def endpointBrownianBridge (T b t : ℝ) (ω : GaussianCoefficientSpace) : ℝ :=
  actualIntervalBridge T t ω + t / T * b

/-- Flat barrier event for the actual bridge coefficient law. -/
def bridgeFlatEvent (T b q : ℝ) : Set GaussianCoefficientSpace :=
  {ω | ∀ t ∈ Set.Icc (0 : ℝ) T, endpointBrownianBridge T b t ω ≤ q}

/-- Standard reflection formula supplied explicitly as an external theorem parameter. -/
def BridgeReflectionInput : Prop :=
  ∀ T b q : ℝ, 0 < T → 0 < q → b < q →
    gaussianCoefficientLaw.real (bridgeFlatEvent T b q) =
      1 - Real.exp (-(2 * q * (q - b) / T))

/-- The manuscript's curved barrier under the actual bridge law. -/
def bridgeCurvedEvent (T b q d γ : ℝ) : Set GaussianCoefficientSpace :=
  {ω | ∀ t ∈ Set.Icc (0 : ℝ) T,
    endpointBrownianBridge T b t ω ≤ q - (d - t) ^ γ}

theorem endpointBrownianBridge_terminal (T b : ℝ) (hT : 0 < T)
    (ω : GaussianCoefficientSpace) : endpointBrownianBridge T b T ω = b := by
  simp [endpointBrownianBridge, actualIntervalBridge_terminal T hT, hT.ne']

/-- The time reversal in the curved barrier proof is an exact event identity. -/
theorem bridgeCurvedEvent_reverse (H T b q γ : ℝ) (ω : GaussianCoefficientSpace) :
    ω ∈ bridgeCurvedEvent T b q (H + T) γ ↔
      ∀ u ∈ Set.Icc (0 : ℝ) T,
        (H + u) ^ γ ≤ q - endpointBrownianBridge T b (T - u) ω := by
  constructor
  · intro h u hu
    have ht : T - u ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have he : H + T - (T - u) = H + u := by ring
    have hx := h (T - u) ht
    rw [he] at hx
    linarith
  · intro h t ht
    have hu : T - t ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hx := h (T - t) hu
    have he : T - (T - t) = t := by ring
    have he' : H + (T - t) = H + T - t := by ring
    rw [he, he'] at hx
    change endpointBrownianBridge T b t ω ≤ q - (H + T - t) ^ γ
    linarith

end SRWTightness
