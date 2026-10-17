import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
namespace SRWTightness

/-- The real sine vanishes only on a countable null set. -/
theorem sine_nonzero_ae : ∀ᵐ u : ℝ ∂volume, Real.sin u ≠ 0 := by
  have hz : volume (Set.range (fun k : ℤ ↦ (k : ℝ) * Real.pi)) = 0 :=
    (Set.countable_range _).measure_zero volume
  have hae : ∀ᵐ u : ℝ ∂volume, u ∉ Set.range (fun k : ℤ ↦ (k : ℝ) * Real.pi) := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hz
  filter_upwards [hae] with u hu
  intro hs
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
  exact hu ⟨k, hk⟩

end SRWTightness
