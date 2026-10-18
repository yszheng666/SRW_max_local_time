import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open MeasureTheory

namespace SRWTightness

/-- Summable real probability bounds control any countable event cover. -/
theorem countable_cover_real_bound {Ω J : Type*} [MeasurableSpace Ω] [Countable J]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (s : J → Set Ω) (b : J → ℝ)
    (hcover : E ⊆ ⋃ j, s j) (hb : ∀ j, 0 ≤ b j) (hsum : Summable b)
    (hbound : ∀ j, μ.real (s j) ≤ b j) : μ.real E ≤ ∑' j, b j := by
  have hh : μ E ≤ ENNReal.ofReal (∑' j, b j) := by
    calc
      μ E ≤ μ (⋃ j, s j) := measure_mono hcover
      _ ≤ ∑' j, μ (s j) := measure_iUnion_le s
      _ ≤ ∑' j, ENNReal.ofReal (b j) := ENNReal.tsum_le_tsum (fun j ↦
        (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (hb j)).mpr (hbound j))
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg hb hsum).symm
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [Measure.real, ENNReal.toReal_ofReal (tsum_nonneg hb)] using hr

end SRWTightness
