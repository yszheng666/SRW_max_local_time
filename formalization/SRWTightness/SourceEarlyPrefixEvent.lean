import SRWTightness.SourceWalkSuccessEvent
import SRWTightness.ExteriorPathRecord

namespace SRWTightness

/-- The manuscript prefix event G_j uses original root counts, including the single initial root. -/
def sourceEarlyPrefixEvent (t : ℝ) (b : Site) (j : ℕ) : Set Sample :=
  {ω | sourceActualCount t b 0 ω = 1 ∧ ∀ i : ℕ, 0 < i → i ≤ j →
    Real.sqrt (2 * (sourceActualCount t b i ω : ℝ)) ≤
      4 + sourceBarrierSlope t * i - (min (i : ℝ) (sourceTotalTime t - i)) ^ (2 / 5 : ℝ)}

/-- Any exterior representation of the original prefix counts represents G_j itself. -/
theorem source_early_prefix_event_of_counts (t : ℝ) (b : Site) (j : ℕ)
    (Z : Sample → ExteriorPathRecord) (g : ExteriorPathRecord → ℕ → ℕ)
    (hg : ∀ ω : Sample, ∀ i ≤ j, g (Z ω) i = sourceActualCount t b i ω) :
    ∃ G : Set ExteriorPathRecord, sourceEarlyPrefixEvent t b j = Z ⁻¹' G := by
  let G : Set ExteriorPathRecord := {h | g h 0 = 1 ∧ ∀ i : ℕ, 0 < i → i ≤ j →
    Real.sqrt (2 * (g h i : ℝ)) ≤
      4 + sourceBarrierSlope t * i - (min (i : ℝ) (sourceTotalTime t - i)) ^ (2 / 5 : ℝ)}
  refine ⟨G, ?_⟩
  ext ω
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [hg ω 0 (Nat.zero_le j)]
  constructor
  · rintro ⟨h0, hh⟩
    refine ⟨h0, ?_⟩
    intro i hi hij
    rw [hg ω i hij]
    exact hh i hi hij
  · rintro ⟨h0, hh⟩
    refine ⟨h0, ?_⟩
    intro i hi hij
    have hp := hh i hi hij
    rwa [hg ω i hij] at hp

end SRWTightness
