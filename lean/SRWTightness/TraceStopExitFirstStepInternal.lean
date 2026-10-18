import SRWTightness.CompetingExitPath
import SRWTightness.ReturnTime

open MeasureTheory

namespace SRWTightness

/-- Positive-return escape with a prescribed exit is the first-step competing exit atom. -/
theorem trace_stop_exit_event_first_step (D K : Finset Site) (hKD : K ⊆ D)
    (x e : Site) (hx : x ∈ K) (he : e ∉ D) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) :
    (domainExit D x ω < setHittingTime K x 1 ω ∧ domainExitLocation D x ω = e) ↔
      domainExitLocation (D \ K) (x + step (ω 0)) (shift 1 ω) = e := by
  have hf : domainExit D (x + step (ω 0)) (shift 1 ω) ≠ ⊤ := by
    rw [domainExit_first_step D x (hKD hx) ω] at hfin
    exact (WithTop.add_ne_top.mp hfin).2
  rw [exit_before_return_first_step D K x (hKD hx) ω,
    domainExitLocation_first_step D x (hKD hx) ω hfin]
  exact (competing_exit_atom_event_iff D K hKD _ e he _ hf).symm

/-- The actual joint terminal escape/exit atom is the average of first-step competing exit atoms. -/
theorem trace_stop_exit_probability_first_step_internal (D K : Finset Site) (hKD : K ⊆ D)
    (x e : Site) (hx : x ∈ K) (he : e ∉ D) :
    traceStopExitProbability D K x e =
      (1 / 4 : ℝ) * ∑ d : Direction, traceExitProbability (D \ K) (x + step d) e := by
  classical
  let E : Set Sample := {ω | domainExit D x ω < setHittingTime K x 1 ω ∧
    domainExitLocation D x ω = e}
  have hE : MeasurableSet E :=
    (measurableSet_lt (domainExit_isStoppingTime D x).measurable'
      (setHittingTime_isStoppingTime K x 1).measurable').inter
        ((measurable_domainExitLocation D x) (measurableSet_singleton e))
  have hprob : pathLaw.real E = ∫ ω, (if ω ∈ E then (1 : ℝ) else 0) ∂pathLaw := by
    simpa [Set.indicator] using (integral_indicator_one (μ := pathLaw) hE).symm
  have hi : (fun ω ↦ if ω ∈ E then (1 : ℝ) else 0) =ᵐ[pathLaw]
      (fun ω ↦ if domainExitLocation (D \ K) (x + step (ω 0)) (shift 1 ω) = e
        then 1 else 0) := by
    filter_upwards [domainExit_ne_top_ae D x] with ω hfin
    simp only [E, Set.mem_setOf_eq, trace_stop_exit_event_first_step D K hKD x e hx he ω hfin]
  change pathLaw.real E = _
  simp_rw [trace_exit_probability_eq_payoff]
  rw [hprob, integral_congr_ae hi, integral_first_step_future
    (fun d ω ↦ if domainExitLocation (D \ K) (x + step d) ω = e then (1 : ℝ) else 0)
    (fun d ↦ (measurable_of_countable (fun y : Site ↦ if y = e then (1 : ℝ) else 0)).comp
      (measurable_domainExitLocation (D \ K) (x + step d)))
    (fun d ↦ integrable_domainExit_payoff (D \ K) (x + step d)
      (fun y ↦ if y = e then 1 else 0))]
  exact integral_direction_average _

end SRWTightness
