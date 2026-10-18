import SRWTightness.AuxiliaryEventComparison
import Mathlib.Tactic.Linarith

open MeasureTheory

namespace SRWTightness

/-- Smooth lower and upper envelopes convert expectation error and boundary error into event error. -/
theorem event_smoothing_comparison {Ω : Type*} [MeasurableSpace Ω]
    (μ κ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure κ]
    (s : Set Ω) (hs : MeasurableSet s) (lower upper : Ω → ℝ)
    (hlμ : Integrable lower μ) (huμ : Integrable upper μ)
    (henvelope : ∀ x, lower x ≤ s.indicator (fun _ ↦ (1 : ℝ)) x ∧
      s.indicator (fun _ ↦ (1 : ℝ)) x ≤ upper x)
    (δ b : ℝ)
    (hlerror : |(∫ x, lower x ∂μ) - ∫ x, lower x ∂κ| ≤ δ)
    (huerror : |(∫ x, upper x ∂μ) - ∫ x, upper x ∂κ| ≤ δ)
    (hlboundary : κ.real s - (∫ x, lower x ∂κ) ≤ b)
    (huboundary : (∫ x, upper x ∂κ) - κ.real s ≤ b) :
    |μ.real s - κ.real s| ≤ δ + b := by
  classical
  have hi : Integrable (s.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const 1).indicator hs
  have hl := integral_mono hlμ hi (fun x ↦ (henvelope x).1)
  have hu := integral_mono hi huμ (fun x ↦ (henvelope x).2)
  have he : (∫ x, s.indicator (fun _ ↦ (1 : ℝ)) x ∂μ) = μ.real s :=
    integral_indicator_one hs
  rw [he] at hl hu
  obtain ⟨hll, hlu⟩ := abs_le.mp hlerror
  obtain ⟨hul, huu⟩ := abs_le.mp huerror
  apply abs_le.mpr
  constructor <;> linarith

end SRWTightness
