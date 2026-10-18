import SRWTightness.KilledChildCountMeanStep
import SRWTightness.DomainExitFutureIntegral
import SRWTightness.ActualRecordKernel

open MeasureTheory

namespace SRWTightness

/-- From an inner entrance, one child completes and all remaining children belong to the future. -/
theorem killed_child_count_inside_ae (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (x : Site) (hx : x ∈ K) :
    (fun ω ↦ ((killedChildIntervals D K C x ω).length : ℝ)) =ᵐ[pathLaw]
      (fun ω ↦ 1 + ((killedChildIntervals D K C (domainExitLocation C x ω)
        (futureAt (domainExit C x) ω)).length : ℝ)) := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hfin
  have hh := congrArg List.length
    (killedChildRecords_inside D K C hKC hCD x hx (fun _ _ ↦ ()) ω hfin)
  simp only [List.length_cons, killedChildRecords_length] at hh
  have hr := congrArg (fun n : ℕ ↦ (n : ℝ)) hh
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] at hr
  linarith

/-- The actual complete-child mean renews exactly at the first child-domain exit. -/
theorem killed_child_count_mean_inside (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (x : Site) (hx : x ∈ K) :
    killedChildCountMean D K C x = 1 + exitPayoff C (killedChildCountMean D K C) x := by
  let f := fun z : Site ↦ fun ω : Sample ↦ ((killedChildIntervals D K C z ω).length : ℝ)
  have hm (z : Site) : Measurable (f z) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_killed_child_count D K C z)
  have hi (z : Site) : Integrable (f z) pathLaw := integrable_killed_child_count D K C z
  have hc : (∫ _ : Sample, (1 : ℝ) ∂pathLaw) = 1 := by simp
  unfold killedChildCountMean
  rw [integral_congr_ae (killed_child_count_inside_ae D K C hKC hCD x hx),
    integral_add (integrable_const (1 : ℝ)) (integrable_domain_exit_future C x f hm hi), hc,
    integral_domain_exit_future C x f hm hi]

end SRWTightness
