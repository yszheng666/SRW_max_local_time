import SRWTightness.ExitMoment

open MeasureTheory

namespace SRWTightness

 theorem measurable_exitSteps (R : ℝ) : Measurable (exitSteps R) :=
  (exitTime_isStoppingTime R).measurable'.untopD 0

set_option maxHeartbeats 1000000 in
/-- The maximum is a measurable observable of the original infinite SRW. -/
theorem measurable_diskMax (R : ℝ) : Measurable (diskMax R) := by
  change Measurable (fun ω ↦ maxLocalTime ω (exitSteps R ω))
  have hm : Measurable (fun p : Sample × ℕ ↦ maxLocalTime p.1 p.2) :=
    measurable_from_prod_countable_left (f := fun p : Sample × ℕ ↦ maxLocalTime p.1 p.2)
      (fun n ↦ measurable_maxLocalTime n)
  exact hm.comp (measurable_id.prodMk (measurable_exitSteps R))

 theorem diskMax_le_exitSteps (R : ℝ) (ω : Sample) :
    diskMax R ω ≤ exitSteps R ω := maxLocalTime_le_time ω _

 theorem integrable_diskMax {R : ℝ} (hR : 0 ≤ R) :
    Integrable (fun ω ↦ (diskMax R ω : ℝ)) pathLaw := by
  apply (integrable_exitSteps hR).mono_nonneg
    (((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_diskMax R)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun ω ↦ Nat.cast_nonneg _)
  · exact Filter.Eventually.of_forall (fun ω ↦ Nat.cast_le.mpr (diskMax_le_exitSteps R ω))

 theorem integral_diskMax_le {R : ℝ} (hR : 0 ≤ R) :
    ∫ ω, (diskMax R ω : ℝ) ∂pathLaw ≤ (R + 1) ^ 2 :=
  (integral_mono (integrable_diskMax hR) (integrable_exitSteps hR)
    (fun ω ↦ Nat.cast_le.mpr (diskMax_le_exitSteps R ω))).trans (integral_exitSteps_le hR)

end SRWTightness
