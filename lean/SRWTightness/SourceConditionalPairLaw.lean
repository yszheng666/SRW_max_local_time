import SRWTightness.ConditionalProductLaw
import SRWTightness.SourcePairBridgeLaw
import SRWTightness.SourceOriginalJointRootBound

open MeasureTheory
namespace SRWTightness

/-- Conditional on the actual exterior record, the common path and both selected auxiliary bridge
families have the conditional path law times their original independent laws. -/
theorem source_conditional_pair_preserving (t : ℝ) (b w : Site) (ν J : ℕ)
    (hbw : b ≠ w) (h : ExteriorPathRecord) :
    MeasurePreserving
      (fun p : Sample × (Site → ℕ → GaussianCoefficientSpace) ↦ (p.1, (p.2 b, p.2 w)))
      (ProbabilityTheory.cond sourceEnlargedLaw
        {p | sourcePairExteriorRecord t b w ν J p.1 = h})
      ((ProbabilityTheory.cond pathLaw {ω | sourcePairExteriorRecord t b w ν J ω = h}).prod
        ((independentBridgeLaw ℕ).prod (independentBridgeLaw ℕ))) := by
  letI : MeasurableSpace ExteriorPathRecord := ⊤
  letI : MeasurableSingletonClass ExteriorPathRecord := ⟨fun _ ↦ trivial⟩
  let H := {ω | sourcePairExteriorRecord t b w ν J ω = h}
  have hH : MeasurableSet H :=
    (measurable_killedExteriorRecord _ _ _ _ _) (measurableSet_singleton h)
  have hh := conditional_preserving (source_pair_projection_preserving b w hbw)
    (H ×ˢ Set.univ) (hH.prod MeasurableSet.univ)
  rw [conditional_product_left] at hh
  have he : (fun p : Sample × (Site → ℕ → GaussianCoefficientSpace) ↦
      (p.1, (p.2 b, p.2 w))) ⁻¹' (H ×ˢ Set.univ) =
      {p | sourcePairExteriorRecord t b w ν J p.1 = h} := by
    ext p
    simp [H]
  rw [he] at hh
  exact hh

end SRWTightness
