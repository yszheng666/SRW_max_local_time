import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.Measure

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- A measurable equivalence transports a density by composition with its inverse. -/
theorem density_pushforward_equiv {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (e : Ω ≃ᵐ Ξ) (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y ↦ f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  simpa only [e.symm_apply_apply] using
    (setLIntegral_map (μ := μ) (f := fun y ↦ f (e.symm y)) (g := e)
      hs (hf.comp e.symm.measurable) e.measurable).symm

/-- Translating a density over an invariant measure translates its argument in the opposite direction. -/
theorem density_pushforward_add {Ω : Type*} [AddGroup Ω] [MeasurableSpace Ω] [MeasurableAdd Ω]
    (μ : Measure Ω) [Measure.IsAddLeftInvariant μ] (m : Ω) (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map (fun x ↦ m + x) = μ.withDensity (fun x ↦ f (-m + x)) := by
  have hh := density_pushforward_equiv μ (MeasurableEquiv.addLeft m) f hf
  simpa only [MeasurableEquiv.coe_addLeft, MeasurableEquiv.symm_addLeft,
    (measurePreserving_add_left μ m).map_eq] using hh

end SRWTightness
