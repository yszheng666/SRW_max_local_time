import SRWTightness.WordFlatteningInternal
import SRWTightness.SourceUpperClosedIndicator

open Filter MeasureTheory
open scoped Classical

namespace SRWTightness

/-- Literal source(4.36), including all half-radius boundary sites and the original
open crossings. -/
theorem source_upper_closed_indicator_radius_internal :
    ∀ᶠ R : ℝ in atTop, ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
        (if (∃ x : Site, Real.sqrt (normSq x) ≤ R / 2 ∧
          Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x) then (1 : ℝ) else 0) ≤
        (if (∃ x : Site, Real.sqrt (normSq x) ≤ R / Real.log R ∧
          Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x) then (1 : ℝ) else 0) +
        (if ω ∈ sourceUpperCrossingEvent (Real.log R) s then (1 : ℝ) else 0) +
        ∑ b ∈ sourceUpperBlockCenters (Real.log R),
          (if ω ∈ sourceUpperDirectBlockSuccess (Real.log R) s b then (1 : ℝ) else 0) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (source_upper_closed_direct_indicator two_level_word_flattening_input_internal),
    eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 2)] with R ht hR hlog
  filter_upwards [ht] with ω hω
  intro s
  have hh := hω s
  rw [source_upper_closed_cutoff_at_radius R s hR,
    source_upper_near_origin_event_at_radius R s hR hlog] at hh
  exact hh

end SRWTightness
