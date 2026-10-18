import SRWTightness.KilledChildCountIntegrable
import SRWTightness.KilledRootPrefixRemoval
import SRWTightness.FirstStepLaw
import SRWTightness.SetHitting

open MeasureTheory

namespace SRWTightness

/-- The ordinary mean of the actual complete-child count in a finite killed domain. -/
noncomputable def killedChildCountMean (D K C : Finset Site) (x : Site) : ℝ :=
  ∫ ω, ((killedChildIntervals D K C x ω).length : ℝ) ∂pathLaw

/-- Starting outside the killing domain leaves no complete child interval. -/
theorem killed_child_count_zero_of_not_mem (D K C : Finset Site) (x : Site)
    (hx : x ∉ D) (ω : Sample) : (killedChildIntervals D K C x ω).length = 0 := by
  have hs : domainSteps D x ω = 0 := by
    simp [domainSteps, domainExit_eq_zero_of_not_mem D x hx ω]
  unfold killedChildIntervals wordChildIntervals
  simp [killedPathWord, hs, scanChildIntervals]

/-- The actual complete-child mean vanishes outside the killing domain. -/
theorem killed_child_count_mean_zero (D K C : Finset Site) (x : Site) (hx : x ∉ D) :
    killedChildCountMean D K C x = 0 := by
  unfold killedChildCountMean
  simp_rw [killed_child_count_zero_of_not_mem D K C x hx]
  simp

/-- Away from an inner entrance, the actual complete-child mean follows the ordinary SRW step. -/
theorem killed_child_count_mean_step (D K C : Finset Site) (x : Site)
    (hxD : x ∈ D) (hxK : x ∉ K) :
    killedChildCountMean D K C x =
      (1 / 4 : ℝ) * ∑ d : Direction, killedChildCountMean D K C (x + step d) := by
  have he : (fun ω ↦ ((killedChildIntervals D K C x ω).length : ℝ)) =ᵐ[pathLaw]
      (fun ω ↦ ((killedChildIntervals D K C (x + step (ω 0)) (shift 1 ω)).length : ℝ)) := by
    filter_upwards [domainExit_ne_top_ae D x] with ω hfin
    have ha : 1 ≤ domainSteps D x ω := by
      by_contra hh
      have hs : domainSteps D x ω = 0 := by omega
      apply position_domain_exit_not_mem D x ω hfin
      simpa only [hs, position_zero_as_zero, add_zero] using hxD
    have hpre : ∀ i < 1, x + position ω i ∉ K := by
      intro i hi
      have hz : i = 0 := by omega
      simpa only [hz, position_zero_as_zero, add_zero] using hxK
    have hh := killedChildIntervals_length_remove_prefix D K C x ω hfin 1 ha hpre
    simpa only [position_one_as_step] using congrArg (fun n : ℕ ↦ (n : ℝ)) hh
  unfold killedChildCountMean
  rw [integral_congr_ae he, integral_first_step_future
    (fun d ω ↦ ((killedChildIntervals D K C (x + step d) ω).length : ℝ))
    (fun d ↦ (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_killed_child_count D K C (x + step d)))
    (fun d ↦ integrable_killed_child_count D K C (x + step d)), integral_direction_average]

end SRWTightness
