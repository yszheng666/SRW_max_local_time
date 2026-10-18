import SRWTightness.ReturnTime
import SRWTightness.EquilibriumAlgebra

open MeasureTheory

namespace SRWTightness

/-- Equilibrium measure with the manuscript's strict exit-before-positive-return definition. -/
noncomputable def equilibriumMeasure (D K : Finset Site) (x : Site) : ℝ :=
  if x ∈ K then pathLaw.real {ω | domainExit D x ω < setHittingTime K x 1 ω} else 0

 theorem equilibriumMeasure_eq_charge (D K : Finset Site) (hKD : K ⊆ D) (x : Site) :
    equilibriumMeasure D K x = equilibriumCharge D K x := by
  classical
  by_cases hx : x ∈ K
  · rw [equilibriumMeasure, equilibriumCharge, if_pos hx, if_pos hx]
    have hs : MeasurableSet {ω | domainExit D x ω < setHittingTime K x 1 ω} :=
      measurableSet_lt (domainExit_isStoppingTime D x).measurable'
        (setHittingTime_isStoppingTime K x 1).measurable'
    have he : (fun ω ↦ if domainExit D x ω < setHittingTime K x 1 ω then (1 : ℝ) else 0) =ᵐ[pathLaw]
        (fun ω ↦ 1 - setHitIndicator D K (x + step (ω 0)) (shift 1 ω)) := by
      filter_upwards [domainExit_ne_top_ae D x] with ω hω
      have hf : domainExit D (x + step (ω 0)) (shift 1 ω) ≠ ⊤ := by
        rw [domainExit_first_step D x (hKD hx) ω] at hω
        exact (WithTop.add_ne_top.mp hω).2
      simp only [exit_before_return_first_step D K x (hKD hx) ω,
        exit_lt_setHittingTime_iff D K hKD _ _ hf]
      unfold setHitIndicator
      by_cases hn : setOccupation D K (x + step (ω 0)) (shift 1 ω) = 0
      · simp [hn]
      · have hp : 1 ≤ setOccupation D K (x + step (ω 0)) (shift 1 ω) := by omega
        simp [hn, hp]
    have hi : pathLaw.real {ω | domainExit D x ω < setHittingTime K x 1 ω} =
        ∫ ω, (if domainExit D x ω < setHittingTime K x 1 ω then (1 : ℝ) else 0) ∂pathLaw := by
      simpa [Set.indicator] using (integral_indicator_one (μ := pathLaw) hs).symm
    rw [hi, integral_congr_ae he]
    rw [integral_first_step_future (fun d ω ↦ 1 - setHitIndicator D K (x + step d) ω)
      (fun d ↦ measurable_const.sub (measurable_setHitIndicator D K _))
      (fun d ↦ integrable_const 1 |>.sub (integrable_setHitIndicator D K _))]
    have hd (d : Direction) : (∫ ω, (1 - setHitIndicator D K (x + step d) ω) ∂pathLaw) =
        1 - setHitProbability D K (x + step d) := by
      rw [integral_sub (integrable_const 1) (integrable_setHitIndicator D K _)]
      simp [setHitProbability]
    simp_rw [hd]
    rw [integral_sub (Integrable.of_finite) (Integrable.of_finite), integral_direction_average]
    norm_num
    exact integral_direction_average _
  · simp [equilibriumMeasure, equilibriumCharge, hx]

/-- Manuscript (2.4), for the actual walk and the original equilibrium measure. -/
theorem green_equilibrium_hitting (D K : Finset Site) (hKD : K ⊆ D) (z : Site) :
    ∑ x ∈ K, killedGreen D z x * equilibriumMeasure D K x =
      pathLaw.real {ω | setHittingTime K z 0 ω < domainExit D z ω} := by
  simp_rw [equilibriumMeasure_eq_charge D K hKD]
  rw [green_mul_equilibriumCharge D K hKD, setHitProbability_eq_hitting]

 theorem green_equilibrium_on_set (D K : Finset Site) (hKD : K ⊆ D)
    (z : Site) (hz : z ∈ K) : ∑ x ∈ K, killedGreen D z x * equilibriumMeasure D K x = 1 := by
  simp_rw [equilibriumMeasure_eq_charge D K hKD]
  exact green_equilibriumCharge_on_set D K hKD z hz

 theorem equilibrium_green_on_set (D K : Finset Site) (hKD : K ⊆ D)
    (z : Site) (hz : z ∈ K) : ∑ x ∈ K, equilibriumMeasure D K x * killedGreen D x z = 1 := by
  simp_rw [equilibriumMeasure_eq_charge D K hKD]
  exact equilibriumCharge_green_on_set D K hKD z hz

end SRWTightness
