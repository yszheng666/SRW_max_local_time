import SRWTightness.FiniteDomain

open MeasureTheory

namespace SRWTightness

/-- Visits before finite-domain exit, with the original half-open convention. -/
noncomputable def domainLocalTime (D : Finset Site) (x y : Site) (ω : Sample) : ℕ :=
  localTime ω (domainSteps D x ω) (y - x)

set_option maxHeartbeats 1000000 in
theorem measurable_domainLocalTime (D : Finset Site) (x y : Site) :
    Measurable (domainLocalTime D x y) := by
  have hm : Measurable (fun p : Sample × ℕ ↦ localTime p.1 p.2 (y - x)) :=
    measurable_from_prod_countable_left (fun n ↦ measurable_localTime n (y - x))
  exact hm.comp (measurable_id.prodMk (measurable_domainSteps D x))

 theorem integrable_domainLocalTime (D : Finset Site) (x y : Site) :
    Integrable (fun ω ↦ (domainLocalTime D x y ω : ℝ)) pathLaw := by
  apply (integrable_domainSteps D x).mono_nonneg
    (((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_domainLocalTime D x y)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun ω ↦ Nat.cast_nonneg _)
  · exact Filter.Eventually.of_forall (fun ω ↦ Nat.cast_le.mpr (localTime_le_time ω _ _))

/-- Probabilistic Green kernel. Its matrix resolvent characterization remains to be proved. -/
noncomputable def killedGreen (D : Finset Site) (x y : Site) : ℝ :=
  ∫ ω, (domainLocalTime D x y ω : ℝ) ∂pathLaw

 theorem killedGreen_nonneg (D : Finset Site) (x y : Site) : 0 ≤ killedGreen D x y :=
  integral_nonneg (fun ω ↦ Nat.cast_nonneg _)

 theorem killedGreen_le_exit_mean (D : Finset Site) (x y : Site) :
    killedGreen D x y ≤ ∫ ω, (domainSteps D x ω : ℝ) ∂pathLaw :=
  integral_mono (integrable_domainLocalTime D x y) (integrable_domainSteps D x)
    (fun ω ↦ Nat.cast_le.mpr (localTime_le_time ω _ _))

end SRWTightness
