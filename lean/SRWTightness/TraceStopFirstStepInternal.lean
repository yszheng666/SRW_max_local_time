import SRWTightness.ExternalKilledExitDecomposition
import SRWTightness.EquilibriumProbability

namespace SRWTightness

/-- The actual positive-return escape probability is the ordinary first-step competing exit mass. -/
theorem trace_stop_probability_first_step_internal (D K : Finset Site) (hKD : K ⊆ D)
    (x : Site) (hx : x ∈ K) :
    traceStopProbability D K x =
      (1 / 4 : ℝ) * ∑ d : Direction, competingExitMass D K (x + step d) := by
  have he : traceStopProbability D K x = equilibriumMeasure D K x := by
    simp only [traceStopProbability, equilibriumMeasure, if_pos hx]
  rw [he, equilibriumMeasure_eq_charge D K hKD, equilibriumCharge, if_pos hx]
  simp_rw [competingExitMass_eq_one_sub_hit D K hKD]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  norm_num [Direction]
  ring

end SRWTightness
