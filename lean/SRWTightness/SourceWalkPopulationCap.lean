import SRWTightness.SourceRootCoarseCounts
import SRWTightness.SourceWalkSuccessEvent

open Filter
namespace SRWTightness

/-- The original walk's single-root coarse event bounds every actual count by eight t squared. -/
theorem source_walk_population_cap :
    ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (ω : Sample),
      sourceActualCount t b 0 ω = 1 → sourceWalkCoarseBand t b ω →
      ∀ j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1,
        (sourceActualCount t b j ω : ℝ) ≤ 8 * t ^ 2 := by
  filter_upwards [source_coarse_root_population_cap, source_root_gw_horizon_large] with t ht hN
  intro b ω hroot hbar j hj
  let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
  have hdepth : 0 < sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
    have hh := hN.1
    omega
  have hlen : (sourceActualForest t b ∅ ω).length = 1 := by
    rw [source_actual_forest_length, hroot]
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp hlen
  have hcoarse := (source_actual_forest_coarse_band t b ∅ hdepth ω r hr).mpr hbar
  have hcap := ht (Mark ∅) r hcoarse.1 (n - j) (Nat.sub_le n j)
  have hpop := source_actual_forest_population t b ∅ hdepth ω r hr j hj
  rw [finite_record_gw_population _ r j hj] at hpop
  change (finiteRecordLevelPopulation n r (n - j) : ℝ) ≤ 8 * t ^ 2 at hcap
  rwa [hpop] at hcap

end SRWTightness
