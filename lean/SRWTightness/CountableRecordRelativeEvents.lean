import SRWTightness.CountableRecordEventComparison

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- Two finite laws with uniform relative record-atom bounds have the same bounds on every event. -/
theorem countable_record_relative_events {Ω Γ R : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [Countable R]
    (μ : Measure Ω) (κ : Measure Γ) [IsFiniteMeasure μ] [IsFiniteMeasure κ]
    (f : Ω → R) (g : Γ → R) (L U : ℝ) (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hf : ∀ r, MeasurableSet (f ⁻¹' {r})) (hg : ∀ r, MeasurableSet (g ⁻¹' {r}))
    (h : ∀ r, L * κ.real (g ⁻¹' {r}) ≤ μ.real (f ⁻¹' {r}) ∧
      μ.real (f ⁻¹' {r}) ≤ U * κ.real (g ⁻¹' {r})) (s : Set R) :
    L * κ.real (g ⁻¹' s) ≤ μ.real (f ⁻¹' s) ∧
      μ.real (f ⁻¹' s) ≤ U * κ.real (g ⁻¹' s) := by
  have hh := countable_record_event_comparison μ f (fun r ↦ κ (g ⁻¹' {r})) s
    (ENNReal.ofReal L) (ENNReal.ofReal U) (fun r _ ↦ hf r) (fun r _ ↦ ?_)
  · rw [tsum_measure_preimage_singleton s.to_countable (fun r _ ↦ hg r)] at hh
    constructor
    · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL, measureReal_def] using
        ENNReal.toReal_mono (measure_ne_top μ _) hh.1
    · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hU, measureReal_def] using
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top κ _)) hh.2
  · constructor
    · simpa only [ENNReal.ofReal_mul hL, ofReal_measureReal (measure_ne_top _ _)] using
        ENNReal.ofReal_le_ofReal (h r).1
    · simpa only [ENNReal.ofReal_mul hU, ofReal_measureReal (measure_ne_top _ _)] using
        ENNReal.ofReal_le_ofReal (h r).2

end SRWTightness
