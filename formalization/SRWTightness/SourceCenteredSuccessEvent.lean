import SRWTightness.SourceSiteBridgeLaw
import SRWTightness.SourceObservationTime

namespace SRWTightness

/-- The source cutoff condition uniquely determines the fine observation level. -/
theorem source_observation_level_unique (t A : ℝ) (I J : ℕ)
    (hI : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I)
    (hJ : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ J) :
    I = J := Nat.le_antisymm
      ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))

/-- The success event at a site's own center, independent of a subtype witness. -/
def sourceCenteredSuccessEvent (t A γ : ℝ) (b : Site) (I : ℕ) :
    Set (Sample × (Site → ℕ → GaussianCoefficientSpace)) :=
  {p | ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
    (z : Site) = b ∧ p ∈ sourceSiteSuccessEvent t A γ b I z}

/-- Every witness for the center gives exactly the same source success event. -/
theorem source_centered_success_event_eq (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (hz : (z : Site) = b) :
    sourceCenteredSuccessEvent t A γ b I = sourceSiteSuccessEvent t A γ b I z := by
  ext p
  constructor
  · rintro ⟨z', hz', hp⟩
    have he : z' = z := Subtype.ext (hz'.trans hz.symm)
    simpa only [he] using hp
  · exact fun hp ↦ ⟨z, hz, hp⟩

end SRWTightness
