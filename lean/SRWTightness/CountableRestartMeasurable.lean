import SRWTightness.HistoryRestartIntegral

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- A measurable functional restarted at an observed countable state stays measurable. -/
theorem measurable_countable_state_restart (ξ : Sample → Site) (hξ : Measurable ξ)
    (n : ℕ) (f : Site → Sample → ℝ≥0∞) (hf : ∀ z, Measurable (f z)) :
    Measurable (fun ω ↦ f (ξ ω) (shift n ω)) := by
  have hp : Measurable (fun ω ↦ (ξ ω, shift n ω)) := hξ.prodMk (measurable_shift n)
  have hj : Measurable (fun v : Site × Sample ↦ f v.1 v.2) :=
    measurable_from_prod_countable_right hf
  exact hj.comp hp

end SRWTightness
