import SRWTightness.RecordExitDisintegration
import SRWTightness.CompetingEntranceLaw

open MeasureTheory

namespace SRWTightness

/-- The actual entrance/future probability integrates the future event against entrance kernel U. -/
theorem competing_entrance_future_integral (D K : Finset Site) (x : Site)
    (t : Site → Set Sample) (ht : ∀ z, MeasurableSet (t z)) :
    pathLaw {ω | domainExitLocation (D \ K) x ω ∈ K ∧
      futureAt (domainExit (D \ K) x) ω ∈ t (domainExitLocation (D \ K) x ω)} =
      ∫⁻ z, pathLaw (t z) ∂competingEntranceLaw D K x := by
  have ht' : ∀ z, MeasurableSet (if z ∈ K then t z else ∅) := by
    intro z
    split_ifs
    · exact ht z
    · exact MeasurableSet.empty
  have hs : recordExitSlice (D \ K) x (fun _ ↦ ()) () =
      pathLaw.map (domainExitLocation (D \ K) x) := by
    simp [recordExitSlice]
  calc
    _ = pathLaw {ω | (fun _ : PathWord ↦ ()) (killedPathWord (D \ K) x ω) = () ∧
        futureAt (domainExit (D \ K) x) ω ∈
          (if domainExitLocation (D \ K) x ω ∈ K then
            t (domainExitLocation (D \ K) x ω) else ∅)} := by
      congr 1
      ext ω
      by_cases hk : domainExitLocation (D \ K) x ω ∈ K <;> simp [hk]
    _ = ∫⁻ z, pathLaw (if z ∈ K then t z else ∅)
        ∂recordExitSlice (D \ K) x (fun _ ↦ ()) () :=
      killed_record_future_exit_integral (D \ K) x (fun _ ↦ ()) () _ ht'
    _ = _ := by
      rw [hs, competingEntranceLaw, ← lintegral_indicator (Finset.measurableSet K)]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ K <;> simp [hz, Set.indicator]

end SRWTightness
