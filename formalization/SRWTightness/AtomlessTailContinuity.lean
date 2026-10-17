import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open MeasureTheory Filter
open scoped Topology
namespace SRWTightness

/-- A finite real measure has a continuous closed tail at every point with zero singleton mass. -/
theorem measure_real_tail_continuousAt (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℝ) (hc : μ {c} = 0) : ContinuousAt (fun y ↦ μ.real (Set.Ici y)) c := by
  have hne : ∀ᵐ x ∂μ, x ≠ c := by
    simpa only [ae_iff, not_not, Set.setOf_eq_eq_singleton] using hc
  have he : ∀ᵐ x ∂μ, ∀ᶠ y in nhds c, x ∈ Set.Ici y ↔ x ∈ Set.Ici c := by
    filter_upwards [hne] with x hx
    rcases lt_or_gt_of_ne hx with hxc | hcx
    · filter_upwards [isOpen_Ioi.mem_nhds hxc] with y hy
      change x < y at hy
      change y ≤ x ↔ c ≤ x
      exact iff_of_false (not_le_of_gt hy) (not_le_of_gt hxc)
    · filter_upwards [isOpen_Iio.mem_nhds hcx] with y hy
      change y < x at hy
      change y ≤ x ↔ c ≤ x
      exact iff_of_true hy.le hcx.le
  have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (nhds c)
    measurableSet_Ici (fun _ ↦ measurableSet_Ici) he
  simpa only [ContinuousAt, Measure.real, Function.comp_def] using
    (ENNReal.continuousAt_toReal (measure_ne_top μ _)).tendsto.comp hlim

end SRWTightness
