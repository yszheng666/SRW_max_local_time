import SRWTightness.FiniteLastVisitCountInput
import SRWTightness.KilledChildCountMeanRenewal
import SRWTightness.FiniteExcursionMeanCharge

open MeasureTheory

namespace SRWTightness

/-- The entire original finite last-visit count input is internally proved on the actual walk. -/
theorem finite_last_visit_count_input_internal : FiniteLastVisitCountInput := by
  intro D K C hKC hCD x
  refine ⟨integrable_killed_child_count D K C x, ?_⟩
  change killedChildCountMean D K C x = _
  exact finite_excursion_mean_charge D K C hKC hCD (killedChildCountMean D K C)
    (killed_child_count_mean_zero D K C)
    (fun y hy hyK ↦ killed_child_count_mean_step D K C y hy hyK)
    (fun y hy ↦ killed_child_count_mean_inside D K C hKC hCD y hy) x

end SRWTightness
