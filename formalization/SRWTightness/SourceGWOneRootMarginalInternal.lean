import SRWTightness.GeometricGWOneRootMarginalInternal
import SRWTightness.SourceGWOneRootMarginal

open MeasureTheory

namespace SRWTightness

/-- The literal original one-root power-ratio formula has no external marginal premise. -/
theorem source_gw_one_root_marginal_internal (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} =
      (j : ℝ) ^ (k - 1) / ((j : ℝ) + 1) ^ (k + 1) :=
  source_gw_one_root_marginal geometric_gw_one_root_marginal_input_internal j k hj hk

/-- The following original exponential population bound is also internally proved. -/
theorem source_gw_one_root_exponential_bound_internal (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} ≤
      Real.exp (-(k : ℝ) / ((j : ℝ) + 1)) :=
  source_gw_one_root_exponential_bound geometric_gw_one_root_marginal_input_internal j k hj hk

end SRWTightness
