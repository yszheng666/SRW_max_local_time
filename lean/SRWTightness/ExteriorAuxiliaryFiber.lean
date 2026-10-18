import SRWTightness.ExternalExteriorBridge
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory
namespace SRWTightness

/-- Independent auxiliary variables keep their original law after conditioning on an exterior atom. -/
theorem exterior_bridge_auxiliary_fiber (hF : ExteriorBridgeFactorizationInput)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (D K C : Finset Site) (label : Site → Bool) (x : Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D K C label x ω = h})
    (us : List PathWord) (hlen : us.length = h.1.length) (s : Set Ξ) :
    (pathLaw.prod μ).real
      ({ω | killedChildRecords D K C x (fun _ w ↦ w) ω = us ∧
        killedExteriorRecord D K C label x ω = h} ×ˢ s) /
      pathLaw.real {ω | killedExteriorRecord D K C label x ω = h} =
        exteriorBridgeWordProduct C h us * μ.real s := by
  rw [measureReal_prod_prod]
  calc
    _ = (pathLaw.real {ω | killedChildRecords D K C x (fun _ w ↦ w) ω = us ∧
      killedExteriorRecord D K C label x ω = h} /
      pathLaw.real {ω | killedExteriorRecord D K C label x ω = h}) * μ.real s := by ring
    _ = _ := by rw [hF D K C label x hKC hCD h hh us hlen]

end SRWTightness
