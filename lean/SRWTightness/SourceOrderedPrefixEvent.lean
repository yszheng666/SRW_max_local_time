import SRWTightness.SourceCommonOrderedForest

namespace SRWTightness

/-- The original prefix barrier as a set of ordered common records. -/
def sourceOrderedPrefixRecords (t : ℝ) (j : ℕ) : Set (FiniteExcursionRecord WordMark j) :=
  {r | ∀ k : ℕ, 0 < k → k ≤ j →
    geometricGWHeight (finiteRecordPopulationList j r) k ≤
      4 + sourceBarrierSlope t * k -
        (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ)}

/-- The original prefix event is exactly selection of a single barrier-admissible ordered tree. -/
theorem source_ordered_prefix_event_iff (t : ℝ) (b : Site) (K : Finset Site) (j : ℕ)
    (ω : Sample) :
    ω ∈ sourceEarlyPrefixEvent t b j ↔
      ∃ r ∈ sourceOrderedPrefixRecords t j, sourceCommonOrderedForest t b K j ω = [r] := by
  constructor
  · intro hω
    obtain ⟨r, hr, hbar⟩ := source_common_ordered_prefix t b K j ω hω
    exact ⟨r, hbar, hr⟩
  · rintro ⟨r, hbar, hr⟩
    constructor
    · rw [← source_common_ordered_forest_length t b K j ω, hr]
      rfl
    · intro k hk hkj
      have hh := hbar k hk hkj
      unfold geometricGWHeight at hh
      rw [source_common_ordered_forest_population t b K j ω r hr k hkj] at hh
      exact hh

end SRWTightness
