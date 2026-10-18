import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- A density depending only on a measurable image commutes with taking that image law. -/
theorem density_map_pullback {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f)
    (ρ : β → ℝ≥0∞) (hρ : Measurable ρ) :
    (μ.withDensity (fun x ↦ ρ (f x))).map f = (μ.map f).withDensity ρ := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, setLIntegral_map hs hρ hf]

end SRWTightness
