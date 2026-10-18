import SRWTightness.KilledChildCountMeanStep
import SRWTightness.NatCountTailMean

open MeasureTheory

namespace SRWTightness

/-- The actual complete-child mean is its convergent positive-count tail series. -/
theorem killed_child_count_mean_tail_series (D K C : Finset Site) (x : Site) :
    Summable (fun n : ℕ ↦ pathLaw.real {ω | n + 1 ≤ (killedChildIntervals D K C x ω).length}) ∧
      killedChildCountMean D K C x =
        ∑' n : ℕ, pathLaw.real {ω | n + 1 ≤ (killedChildIntervals D K C x ω).length} :=
  nat_count_mean_tail_series pathLaw (fun ω ↦ (killedChildIntervals D K C x ω).length)
    (measurable_killed_child_count D K C x) (integrable_killed_child_count D K C x)

end SRWTightness
