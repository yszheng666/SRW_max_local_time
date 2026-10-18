import SRWTightness.SourceRemainingForestCap
import SRWTightness.SourceLongFineRecord

open Filter
namespace SRWTightness

/-- The remaining success band alone controls the full fine-record error after the split. -/
theorem source_remaining_forest_error (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ ν : ℕ,
      ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (a : ℝ) (K : Finset Site), 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      ∀ rs : List (FiniteExcursionRecord (Mark K)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))),
      rs.length ≤ sourceEarlyRootCap t ν →
      forestPopulationList _ rs ∈ sourceContinuationBand t ν
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) →
      (rs.map (sourceLongFineError B W t a K ν)).sum ≤ sourceForestQuadraticError B W 8 t := by
  filter_upwards [source_remaining_forest_population_cap,
    eventually_ge_atTop (Real.exp 1)] with t hpop ht
  intro ν hν a K ha hcut rs hk hb
  have hh := source_forest_quadratic_count_error B W 8 (sourceLowerRadius t) a t
    hB hW (by norm_num) (sourceLowerRadius_pos t) ha ht hcut _ rs
    (hpop ν hν (Mark K) rs hk hb)
  exact hh

end SRWTightness
