import SRWTightness.SourceWalkSuccessEvent
import SRWTightness.SourceDeficitBand

open Filter
open scoped Topology

namespace SRWTightness

/-- The original coarse success band puts the actual terminal normalization in [t,2t]. -/
theorem source_walk_normalization_bounds :
    ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (ω : Sample), sourceWalkCoarseBand t b ω →
      let k := sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ω
      t ≤ Real.sqrt (2 * (k : ℝ)) ∧ Real.sqrt (2 * (k : ℝ)) ≤ 2 * t := by
  filter_upwards [source_deficit_large_conditions] with t ht
  intro b ω hb
  have hband := hb.2
  have hh := sourceTerminalRoot_bounds t _ ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hband.1 hband.2
  dsimp only [sourceTerminalRoot] at hh
  convert hh using 1 <;> congr 1 <;> ring

end SRWTightness
