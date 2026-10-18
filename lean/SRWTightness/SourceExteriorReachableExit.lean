import SRWTightness.ExteriorReachableExit
import SRWTightness.SourceExteriorEntranceShell

open Filter
namespace SRWTightness

/-- Actual positive source exterior atoms supply reachable exits for every selected long bridge. -/
theorem source_exterior_exit_positive (hF : ExteriorBridgeFactorizationInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ s ∈ h.1, let z := if s.2.1 then w else b
        0 < traceExitProbability (sourceExitDomain m 1 ℓ z (ν - J)) s.2.2.1 s.2.2.2 := by
  filter_upwards [source_exterior_geometry] with t ht
  intro b w ν J hb hw hbw ha hν hform
  obtain ⟨hK₀, hK₁, hCD, hgap₀, hgap₁, _⟩ := ht b w ν J hb hw hbw ha hν hform
  dsimp only
  intro h hh s hs
  have hp := exterior_atom_exit_positive hF _ _ _ _ _ 0 hK₀ hK₁ hCD hgap₀ hgap₁ h hh s hs
  split <;> simp_all

end SRWTightness
