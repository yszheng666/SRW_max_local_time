import SRWTightness.ActualChildRecords
import SRWTightness.RecordExitDisintegration

open MeasureTheory

namespace SRWTightness

theorem shift_zero_path (ω : Sample) : shift 0 ω = ω := by
  funext n
  simp only [shift, Nat.zero_add]

theorem shift_shift_path (ω : Sample) (a b : ℕ) :
    shift b (shift a ω) = shift (a + b) ω := by
  funext n
  simp only [shift, Nat.add_assoc]

/-- From inside K the first mark is the current child killed word, followed by actual renewal. -/
theorem killedChildRecords_inside (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    {R : Type*} (x : Site) (hx : x ∈ K) (F : Site → PathWord → R) (ω : Sample)
    (hparent : domainExit D x ω ≠ ⊤) :
    killedChildRecords D K C x F ω = F x (killedPathWord C x ω) ::
      killedChildRecords D K C (domainExitLocation C x ω) F (futureAt (domainExit C x) ω) := by
  have he0 : domainSteps (D \ K) x ω = 0 := by
    unfold domainSteps
    rw [domainExit_eq_zero_of_not_mem (D \ K) x
      (fun h ↦ (Finset.mem_sdiff.mp h).2 hx) ω]
    rfl
  have hh := killedChildRecords_renewal D K C hKC hCD x F ω 0 (domainSteps C x ω)
    hparent he0.symm (by simp [shift_zero_path]) (by simpa using hx)
  change killedChildRecords D K C x F ω = F x (killedPathWord C x ω) ::
    killedChildRecords D K C (x + position ω (domainSteps C x ω)) F
      (shift (domainSteps C x ω) ω)
  simpa only [position_zero_as_zero, add_zero, shift_zero_path] using hh

/-- From an entrance site, a specified first mark and tail integrate against the actual joint S kernel. -/
theorem killedChildRecords_inside_cons_probability (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) {R : Type*} (x : Site) (hx : x ∈ K)
    (F : Site → PathWord → R) (r : R) (rs : List R) :
    pathLaw {ω | killedChildRecords D K C x F ω = r :: rs} =
      ∫⁻ ξ, pathLaw {ω | killedChildRecords D K C ξ F ω = rs}
        ∂recordExitSlice C x (fun ω ↦ F x (killedPathWord C x ω)) r := by
  rw [← killed_record_future_exit_integral C x (F x) r
    (fun ξ ↦ {ω | killedChildRecords D K C ξ F ω = rs})
    (fun ξ ↦ measurableSet_killedChildRecords_eq D K C ξ F rs)]
  apply measure_congr
  filter_upwards [domainExit_ne_top_ae D x] with ω hω
  change (killedChildRecords D K C x F ω = r :: rs) =
    (F x (killedPathWord C x ω) = r ∧
      killedChildRecords D K C (domainExitLocation C x ω) F
        (futureAt (domainExit C x) ω) = rs)
  rw [killedChildRecords_inside D K C hKC hCD x hx F ω hω]
  exact List.cons.injEq _ _ _ _

end SRWTightness
