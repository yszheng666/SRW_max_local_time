import SRWTightness.SourceGWOneRootMarginalInternal

open MeasureTheory

namespace SRWTightness

/-- The literal original positive-population ratio holds at every generation, including zero. -/
theorem source_gw_one_root_marginal_all_generations (j k : ℕ) (hk : 1 ≤ k) :
    (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} =
      (j : ℝ) ^ (k - 1) / ((j : ℝ) + 1) ^ (k + 1) := by
  by_cases hj : j = 0
  · subst j
    rw [geometric_gw_population_event_real_atom, geometric_gw_head_law_zero]
    by_cases hk1 : k = 1
    · subst k
      simp [measureReal_def]
    · have hp : k - 1 ≠ 0 := by omega
      simp [measureReal_def, hk1, Ne.symm hk1, hp]
  · exact source_gw_one_root_marginal_internal j k (by omega) hk

end SRWTightness
