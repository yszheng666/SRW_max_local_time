import SRWTightness.GeometricGWHeadAtoms
import SRWTightness.GeometricGWGenerationAtoms
import SRWTightness.GeometricGWMarginalSeries
import SRWTightness.ExternalGWOneRootMarginal

open MeasureTheory

namespace SRWTightness

/-- The positive atoms of the actual single-root population law have the critical closed form. -/
theorem geometric_gw_head_one_root_positive_atom (j m : ℕ) (hj : 1 ≤ j) (hm : 1 ≤ m) :
    (geometricGWHeadLaw 1 j).real {m} =
      (1 / ((j : ℝ) + 1) ^ 2) * ((j : ℝ) / ((j : ℝ) + 1)) ^ (m - 1) := by
  induction j generalizing m with
  | zero => omega
  | succ j ih =>
    by_cases hj0 : j = 0
    · subst j
      rw [geometric_gw_head_one_generation, geometricGWOffspringLaw_singleton]
      have he : m + 1 = (m - 1) + 2 := by omega
      rw [he, pow_add]
      norm_num <;> ring
    · have hj1 : 1 ≤ j := by omega
      have hh : (geometricGWHeadLaw 1 (j + 1)).real {m} =
          (1 / ((j : ℝ) + 2) ^ 2) * (((j : ℝ) + 1) / ((j : ℝ) + 2)) ^ (m - 1) := by
        calc
          _ = ∑' n : ℕ, (1 / ((j : ℝ) + 1) ^ 2) *
              ((j : ℝ) / ((j : ℝ) + 1)) ^ n * ((m + n).choose m : ℝ) *
                (1 / 2 : ℝ) ^ (m + n + 1) := by
            rw [geometric_gw_head_positive_mixture j m hm]
            apply tsum_congr
            intro n
            rw [ih (n + 1) hj1 (by omega), geometric_gw_generation_positive_parents_atom]
            simp only [Nat.add_sub_cancel]
            ring
          _ = _ := geometric_gw_marginal_positive_series j m hm
      simpa only [Nat.cast_add, Nat.cast_one,
        show (j : ℝ) + 1 + 1 = (j : ℝ) + 2 by ring] using hh

/-- The entire original one-root marginal input is internally proved on the actual record law. -/
theorem geometric_gw_one_root_marginal_input_internal : GeometricGWOneRootMarginalInput := by
  intro j m hj hm
  rw [geometric_gw_population_event_real_atom]
  exact geometric_gw_head_one_root_positive_atom j m hj hm

end SRWTightness
