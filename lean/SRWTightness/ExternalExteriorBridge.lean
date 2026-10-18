import SRWTightness.ExteriorRecordSupport
import SRWTightness.KilledWordBridge

namespace SRWTightness

/-- Product of actual stopped-word bridge masses in the order of the exterior headers. -/
noncomputable def exteriorBridgeWordProduct (C : Finset Site) (h : ExteriorPathRecord)
    (us : List PathWord) : ℝ :=
  ((h.1.zip us).map (fun p ↦ killedWordBridgeProbability C p.1.2.2.1 p.1.2.2.2 p.2)).prod

/-- Standard finite-chain disintegration after erasing complete stopped segments. This explicit
foundation supplies exact bridge factorization only, with no comparison estimate or source geometry. -/
def ExteriorBridgeFactorizationInput : Prop :=
  ∀ (D K C : Finset Site) (label : Site → Bool) (x : Site), K ⊆ C → C ⊆ D →
    ∀ h : ExteriorPathRecord,
    0 < pathLaw.real {ω | killedExteriorRecord D K C label x ω = h} →
    ∀ us : List PathWord, us.length = h.1.length →
    pathLaw.real {ω | killedChildRecords D K C x (fun _ w ↦ w) ω = us ∧
        killedExteriorRecord D K C label x ω = h} /
      pathLaw.real {ω | killedExteriorRecord D K C label x ω = h} =
        exteriorBridgeWordProduct C h us

/-- The two-domain exterior label is determined by the entrance site, not by an internal duration. -/
def twoDomainExteriorLabel (K₁ : Finset Site) (x : Site) : Bool := decide (x ∈ K₁)

/-- Each header selects the bridge domain of its recorded label. -/
noncomputable def labeledExteriorBridgeWordProduct (C₀ C₁ : Finset Site)
    (h : ExteriorPathRecord) (us : List PathWord) : ℝ :=
  ((h.1.zip us).map (fun p ↦ killedWordBridgeProbability
    (if p.1.2.1 then C₁ else C₀) p.1.2.2.1 p.1.2.2.2 p.2)).prod

end SRWTightness
