import SRWTightness.SourceEarlyPrefixEvent
import SRWTightness.SourceSiteBridgeLaw
import SRWTightness.SourceEarlyRootCap

namespace SRWTightness

/-- Actual continuous site success implies the original prefix event at every permitted level. -/
theorem source_site_success_prefix (t A γ : ℝ) (b : Site) (I j : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hj : j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1)
    (p : Sample × (Site → ℕ → GaussianCoefficientSpace))
    (hp : p ∈ sourceSiteSuccessEvent t A γ b I z) :
    p.1 ∈ sourceEarlyPrefixEvent t b j := by
  have hbar : sourceWalkCoarseBand t b p.1 := hp.2.2.1
  exact ⟨hp.1, fun i hi hij ↦ hbar.1 i hi (hij.trans hj)⟩

/-- A prefix count obeys the manuscript integer cap, including generation zero. -/
theorem source_prefix_count_cap (t : ℝ) (b : Site) (j : ℕ) (ω : Sample)
    (hθ : 0 ≤ sourceBarrierSlope t) (hjtime : (j : ℝ) ≤ sourceTotalTime t)
    (hω : ω ∈ sourceEarlyPrefixEvent t b j) :
    ∀ i ≤ j, sourceActualCount t b i ω ≤ sourceEarlyRootCap t i := by
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    rw [hω.1]
    norm_num [sourceEarlyRootCap]
  · have hir : (i : ℝ) ≤ j := Nat.cast_le.mpr hi
    have hw : 0 ≤ (min (i : ℝ) (sourceTotalTime t - i)) ^ (2 / 5 : ℝ) :=
      Real.rpow_nonneg (le_min (Nat.cast_nonneg _) (by linarith)) _
    have hh := hω.2 i (Nat.pos_of_ne_zero hi0) hi
    exact source_early_root_cap_of_height t i _ hθ (by linarith)

/-- The full original success event supplies the cap needed in the joint-root aggregation. -/
theorem source_site_success_count_cap (t A γ : ℝ) (b : Site) (I j : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hj : j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1)
    (hθ : 0 ≤ sourceBarrierSlope t) (hjtime : (j : ℝ) ≤ sourceTotalTime t)
    (p : Sample × (Site → ℕ → GaussianCoefficientSpace))
    (hp : p ∈ sourceSiteSuccessEvent t A γ b I z) :
    sourceActualCount t b j p.1 ≤ sourceEarlyRootCap t j :=
  source_prefix_count_cap t b j p.1 hθ hjtime
    (source_site_success_prefix t A γ b I j z hj p hp) j le_rfl

end SRWTightness
