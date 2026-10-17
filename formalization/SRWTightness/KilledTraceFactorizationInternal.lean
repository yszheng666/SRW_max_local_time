import SRWTightness.KilledVisitTraceHistory
import SRWTightness.DisjointHistoryFuture

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The complete actual SRW trace factorization follows from disjoint histories and future law. -/
theorem killed_trace_factorization_input_internal : KilledTraceFactorizationInput := by
  classical
  intro D K x e hKD hx ξ hξ
  let E := visitTraceHistoryEvent D K x ξ
  let B : Set Sample := {ω | domainExit D (ξ.getLastD x) ω <
    setHittingTime K (ξ.getLastD x) 1 ω}
  let C : Set Sample := {ω | domainExit D (ξ.getLastD x) ω <
    setHittingTime K (ξ.getLastD x) 1 ω ∧ domainExitLocation D (ξ.getLastD x) ω = e}
  have hE : ∀ n, MeasurableSet[history n] (E n) :=
    measurable_visit_trace_history_event D K x ξ
  have hd : Pairwise (fun n m ↦ Disjoint (E n) (E m)) :=
    visit_trace_history_pairwise_disjoint D K x ξ
  have hB : MeasurableSet B :=
    measurableSet_lt (domainExit_isStoppingTime D _).measurable'
      (setHittingTime_isStoppingTime K _ 1).measurable'
  have hC : MeasurableSet C := hB.inter
    ((measurable_domainExitLocation D _) (measurableSet_singleton e))
  have hp : pathLaw {ω | killedVisitTrace D K x ω = ξ} =
      (∑' n, pathLaw (E n)) * pathLaw B := by
    rw [← disjoint_history_future_mass E hE hd B hB]
    apply measure_congr
    filter_upwards [domainExit_ne_top_ae D x] with ω hfin
    apply propext
    change killedVisitTrace D K x ω = ξ ↔ ω ∈ ⋃ n, E n ∩ (shift n) ⁻¹' B
    simpa only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_setOf_eq, E, B, C]
      using killed_visit_trace_history_iff D K x hKD hx ξ ω hfin
  have hj : pathLaw {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} =
      (∑' n, pathLaw (E n)) * pathLaw C := by
    rw [← disjoint_history_future_mass E hE hd C hC]
    apply measure_congr
    filter_upwards [domainExit_ne_top_ae D x] with ω hfin
    apply propext
    change (killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e) ↔
      ω ∈ ⋃ n, E n ∩ (shift n) ⁻¹' C
    simpa only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_setOf_eq, E, B, C]
      using killed_visit_trace_exit_history_iff D K x e hKD hx ξ ω hfin
  refine ⟨(∑' n, pathLaw (E n)).toReal, ENNReal.toReal_nonneg, ?_, ?_⟩
  · exact congrArg ENNReal.toReal hp |>.trans (ENNReal.toReal_mul)
  · exact congrArg ENNReal.toReal hj |>.trans (ENNReal.toReal_mul)

end SRWTightness
