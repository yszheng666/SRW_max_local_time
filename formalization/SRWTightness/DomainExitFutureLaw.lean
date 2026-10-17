import SRWTightness.RecordExitDisintegration
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

namespace SRWTightness

/-- The actual exit site and restarted future have the exact product law at a finite-domain exit. -/
theorem domain_exit_site_future_law (C : Finset Site) (x : Site) :
    pathLaw.map (fun ω ↦ (domainExitLocation C x ω, futureAt (domainExit C x) ω)) =
      (pathLaw.map (domainExitLocation C x)).prod pathLaw := by
  classical
  have hm : Measurable (fun ω ↦
      (domainExitLocation C x ω, futureAt (domainExit C x) ω)) :=
    (measurable_domainExitLocation C x).prodMk
      (measurable_futureAt (domainExit C x) (domainExit_isStoppingTime C x))
  have hSlice : recordExitSlice C x (fun _ : Sample ↦ ()) () =
      pathLaw.map (domainExitLocation C x) := by simp [recordExitSlice]
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply hm (hs.prod ht), Measure.prod_prod]
  have hE := killed_record_future_exit_integral C x (fun _ : PathWord ↦ ()) ()
    (fun ξ ↦ if ξ ∈ s then t else ∅) (fun ξ ↦ by
      split_ifs
      · exact ht
      · exact MeasurableSet.empty)
  rw [hSlice] at hE
  have hset : (fun ω ↦ (domainExitLocation C x ω, futureAt (domainExit C x) ω)) ⁻¹'
      (s ×ˢ t) = {ω | () = () ∧ futureAt (domainExit C x) ω ∈
        (if domainExitLocation C x ω ∈ s then t else ∅)} := by
    ext ω
    by_cases hξ : domainExitLocation C x ω ∈ s <;> simp [hξ]
  rw [hset, hE]
  have hfun : (fun ξ : Site ↦ pathLaw (if ξ ∈ s then t else ∅)) =
      s.indicator (fun _ ↦ pathLaw t) := by
    funext ξ
    by_cases hξ : ξ ∈ s <;> simp [Set.indicator, hξ]
  rw [hfun, lintegral_indicator_const hs]
  exact mul_comm _ _

end SRWTightness
