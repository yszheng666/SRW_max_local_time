import SRWTightness.SourceSiteBridgeLaw
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory
namespace SRWTightness

/-- Distinct sites retain independent complete auxiliary bridge families on the common source space. -/
theorem source_pair_bridge_projection_preserving (b w : Site) (hbw : b ≠ w) :
    MeasurePreserving (fun β : Site → ℕ → GaussianCoefficientSpace ↦ (β b, β w))
      sourceSiteBridgeLaw ((independentBridgeLaw ℕ).prod (independentBridgeLaw ℕ)) := by
  refine ⟨(measurable_pi_apply b).prodMk (measurable_pi_apply w), ?_⟩
  exact Measure.infinitePi_map_eval_prod (P := fun _ : Site ↦ independentBridgeLaw ℕ) hbw

/-- The common walk and the two selected independent auxiliary families have their exact product law. -/
theorem source_pair_projection_preserving (b w : Site) (hbw : b ≠ w) :
    MeasurePreserving
      (fun p : Sample × (Site → ℕ → GaussianCoefficientSpace) ↦ (p.1, (p.2 b, p.2 w)))
      sourceEnlargedLaw (pathLaw.prod ((independentBridgeLaw ℕ).prod (independentBridgeLaw ℕ))) := by
  exact (MeasurePreserving.id pathLaw).prod (source_pair_bridge_projection_preserving b w hbw)

end SRWTightness
