import SRWTightness.SourceCoarseTerminalForestEvent
import SRWTightness.SourceGWTerminalCount

open Filter

namespace SRWTightness

/-- The source deficit band forces a positive terminal count for all sufficiently large times. -/
theorem source_gw_band_terminal_positive :
    ∀ᶠ t : ℝ in atTop, ∀ (n : ℕ) (g : GeometricGWRecord),
      g ∈ sourceGWCoarseBandEvent t n → 0 < geometricGWPopulation g n := by
  filter_upwards [source_deficit_large_conditions] with t ht
  intro n g hg
  have hb := (sourceTerminalRoot_bounds t
    (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight g n)
    ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hg.2.1 hg.2.2).1
  rw [(source_gw_terminal_count_identity t n g).1] at hb
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  by_contra h
  have hz : geometricGWPopulation g n = 0 := by omega
  simp only [geometricGWHeight, hz, Nat.cast_zero, mul_zero, Real.sqrt_zero] at hb
  linarith

/-- The actual coarse/terminal forest event cannot include the zero-count case excluded in the manuscript. -/
theorem source_coarse_terminal_forest_positive :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (b : Site) (I : ℕ)
      (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (n : ℕ)
      (r : FiniteExcursionRecord
        (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n)
      (y : ℕ → GaussianCoefficientSpace),
      ([r], y) ∈ sourceCoarseTerminalForestEvent t A γ b I z n →
        0 < geometricGWPopulation (finiteRecordPopulationList n r) n := by
  filter_upwards [source_gw_band_terminal_positive] with t ht
  intro A γ b I z n r y h
  obtain ⟨v, hv, hg, _⟩ := h
  have he : r = v := by simpa using hv
  subst v
  exact ht n _ hg

end SRWTightness
