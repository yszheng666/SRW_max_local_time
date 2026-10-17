import SRWTightness.SourceFineForestPopulation
import SRWTightness.SourceWalkPopulationCap
import SRWTightness.SourceForestErrorDecay

open MeasureTheory Filter
namespace SRWTightness

/-- Actual successful source forests satisfy the vanishing fine-record error bound at every root level. -/
theorem source_actual_fine_error (hF : TwoLevelWordFlatteningInput)
    (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceCandidateAnnulus (Real.exp t), ∀ (K : Finset Site) (ν : ℕ),
      ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ a : ℝ, 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      ∀ᵐ ω ∂pathLaw, sourceActualCount t b 0 ω = 1 → sourceWalkCoarseBand t b ω →
        ((sourceActualFineForest t b K ν ω).map (sourceLongFineError B W t a K ν)).sum ≤
          sourceForestQuadraticError B W 8 t := by
  filter_upwards [source_walk_population_cap, source_candidate_exit_domains,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (Real.exp 1)] with t hcap hD hm ht
  intro b hb K ν hν a ha hcut
  filter_upwards [source_fine_forest_population hF t b K ν hm hν (hD b hb 0)] with ω hpop
  intro hroot hbar
  have hcounts : ∀ j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1),
      (forestLevelPopulation (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        (sourceActualFineForest t b K ν ω) j : ℝ) ≤ 8 * t ^ 2 := by
    intro j hj
    rw [hpop j hj]
    exact hcap b ω hroot hbar _ (by omega)
  exact source_forest_quadratic_count_error B W 8 (sourceLowerRadius t) a t hB hW
    (by norm_num) (sourceLowerRadius_pos t) ha ht hcut _ (sourceActualFineForest t b K ν ω) hcounts

end SRWTightness
