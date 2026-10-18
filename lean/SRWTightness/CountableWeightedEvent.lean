import SRWTightness.CountableRecordFunctional

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- A countable fiber bound is integrated against the original law, without factorizing its coordinates. -/
theorem countable_weighted_event_bound {Ω R : Type*} [MeasurableSpace Ω]
    [MeasurableSpace R] [MeasurableSingletonClass R] [Countable R]
    (μ κ : Measure Ω) (f : Ω → R) (hf : Measurable f) (w : R → ℝ≥0∞)
    (s : Set R) (U : ℝ≥0∞)
    (h : ∀ r ∈ s, κ (f ⁻¹' {r}) ≤ U * (w r * μ (f ⁻¹' {r}))) :
    κ (f ⁻¹' s) ≤ U * ∫⁻ ω, s.indicator w (f ω) ∂μ := by
  classical
  let g : R → ℝ≥0∞ := s.indicator (fun _ ↦ 1)
  have hg : ∀ r, r ∉ s → g r = 0 := by intro r hr; simp [g, hr]
  have hb := (countable_record_functional_comparison κ f hf
    (fun r ↦ w r * μ (f ⁻¹' {r})) g s hg 0 U (fun r hr ↦ ⟨by simp, h r hr⟩)).2
  have hs : MeasurableSet s := s.to_countable.measurableSet
  have hleft : (∫⁻ ω, g (f ω) ∂κ) = κ (f ⁻¹' s) := by
    simpa only [g, one_mul] using (lintegral_indicator_const_comp (μ := κ) hf hs 1)
  have hright : (∫⁻ ω, s.indicator w (f ω) ∂μ) =
      ∑' r, g r * (w r * μ (f ⁻¹' {r})) := by
    rw [show (fun ω ↦ s.indicator w (f ω)) = (s.indicator w) ∘ f from rfl,
      lintegral_comp (measurable_of_countable _) hf, lintegral_countable']
    apply tsum_congr
    intro r
    rw [Measure.map_apply hf (measurableSet_singleton r)]
    by_cases hr : r ∈ s <;> simp [g, hr]
  rwa [hleft, ← hright] at hb

end SRWTightness
