import SRWTightness.StoppedPathWord
import SRWTightness.RecordExitSlice

open MeasureTheory

namespace SRWTightness

/-- Each joint exit-slice atom retains both the record event and the exit position. -/
theorem recordExitSlice_singleton {R : Type*} (D : Finset Site) (x : Site)
    (F : Sample → R) (r : R) (ξ : Site) :
    recordExitSlice D x F r {ξ} =
      pathLaw {ω | F ω = r ∧ domainExitLocation D x ω = ξ} := by
  rw [recordExitSlice,
    Measure.map_apply (measurable_domainExitLocation D x) (measurableSet_singleton ξ),
    Measure.restrict_apply ((measurable_domainExitLocation D x) (measurableSet_singleton ξ))]
  apply measure_congr
  filter_upwards [] with ω
  change (domainExitLocation D x ω = ξ ∧ F ω = r) =
    (F ω = r ∧ domainExitLocation D x ω = ξ)
  exact propext and_comm

/-- The actual child record and exit site remain joint when the post-exit path is factored out. -/
theorem killed_record_exit_future_factorization {R : Type*} (D : Finset Site) (x : Site)
    (F : PathWord → R) (r : R) (ξ : Site) (t : Set Sample) (ht : MeasurableSet t) :
    pathLaw ({ω | F (killedPathWord D x ω) = r ∧ domainExitLocation D x ω = ξ} ∩
      (futureAt (domainExit D x)) ⁻¹' t) =
      recordExitSlice D x (fun ω ↦ F (killedPathWord D x ω)) r {ξ} * pathLaw t := by
  rw [recordExitSlice_singleton]
  have hh := killed_word_future_factorization D x
    {w | F w = r ∧ x + position (wordPath w) w.length = ξ} t ht
  simpa only [Set.mem_setOf_eq, killedPathWord_exitLocation] using hh

end SRWTightness
