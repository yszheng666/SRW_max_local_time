import SRWTightness.GeometricGWHeadLaw
import SRWTightness.GeometricGWOneGeneration
import SRWTightness.GeometricGWGenerationZero
import SRWTightness.CountableNatBindAtoms

open MeasureTheory

namespace SRWTightness

/-- The one-generation single-root head law is the original critical offspring law. -/
theorem geometric_gw_head_one_generation : geometricGWHeadLaw 1 1 = geometricGWOffspringLaw := by
  rw [show 1 = 0 + 1 by rfl, geometric_gw_head_law_step, geometric_gw_head_law_zero,
    Measure.dirac_bind (measurable_of_countable _) 1, geometric_gw_generation_one]

/-- Original head-population atoms evolve by the exact countable generation mixture. -/
theorem geometric_gw_head_step_atom (j m : ℕ) :
    (geometricGWHeadLaw 1 (j + 1)).real {m} =
      ∑' k : ℕ, (geometricGWHeadLaw 1 j).real {k} * (geometricGWGenerationLaw k).real {m} := by
  rw [geometric_gw_head_law_step, countable_nat_bind_real_atom]

/-- The countable head-population mixture has summable real atom weights. -/
theorem geometric_gw_head_step_atom_summable (j m : ℕ) :
    Summable (fun k : ℕ ↦ (geometricGWHeadLaw 1 j).real {k} *
      (geometricGWGenerationLaw k).real {m}) :=
  countable_nat_bind_atom_summable _ _ _

/-- At a positive target population, zero parents vanish and the mixture starts with one parent. -/
theorem geometric_gw_head_positive_mixture (j m : ℕ) (hm : 1 ≤ m) :
    (geometricGWHeadLaw 1 (j + 1)).real {m} =
      ∑' n : ℕ, (geometricGWHeadLaw 1 j).real {n + 1} *
        (geometricGWGenerationLaw (n + 1)).real {m} := by
  rw [geometric_gw_head_step_atom, (geometric_gw_head_step_atom_summable j m).tsum_eq_zero_add]
  rw [geometric_gw_generation_zero_positive_atom m hm, mul_zero, zero_add]

/-- Reading the actual chronological endpoint event gives exactly the head-population atom. -/
theorem geometric_gw_population_event_real_atom (k j m : ℕ) :
    (geometricGWRecordLaw k j).real {r | geometricGWPopulation r j = m} =
      (geometricGWHeadLaw k j).real {m} := by
  have hh : ((geometricGWRecordLaw k j).map (fun r ↦ geometricGWPopulation r j)).real {m} =
      (geometricGWRecordLaw k j).real {r | geometricGWPopulation r j = m} := by
    rw [measureReal_def, Measure.map_apply (measurable_of_countable _)
      (measurableSet_singleton m)]
    rfl
  rw [geometric_gw_final_population_law] at hh
  exact hh.symm

end SRWTightness
