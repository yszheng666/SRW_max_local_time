import SRWTightness.GeometricGWLaw

open MeasureTheory

namespace SRWTightness

/-- Standard critical geometric branching marginal, explicitly supplied on the actual record law. -/
def GeometricGWOneRootMarginalInput : Prop :=
  ∀ j k : ℕ, 1 ≤ j → 1 ≤ k →
    (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} =
      (1 / ((j : ℝ) + 1) ^ 2) * ((j : ℝ) / ((j : ℝ) + 1)) ^ (k - 1)

end SRWTightness
