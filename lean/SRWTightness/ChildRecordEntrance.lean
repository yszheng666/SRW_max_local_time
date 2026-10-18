import SRWTightness.InsideChildRecord
import SRWTightness.CompetingEntranceFuture

open MeasureTheory

namespace SRWTightness

/-- Before a successful first entrance no record is created, so the entire record list is unchanged. -/
theorem killedChildRecords_cut_at_entrance (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) {R : Type*} (x : Site) (F : Site → PathWord → R) (ω : Sample)
    (hparent : domainExit D x ω ≠ ⊤) (a : ℕ)
    (haeq : a = domainSteps (D \ K) x ω) (hentry : x + position ω a ∈ K) :
    killedChildRecords D K C x F ω =
      killedChildRecords D K C (x + position ω a) F (shift a ω) := by
  have ha : a ≤ domainSteps D x ω := by
    rw [haeq]
    exact (subdomain_exit_bounds D (D \ K) Finset.sdiff_subset x ω hparent).2
  have hf := (shifted_subdomain_exit_bounds D D (fun _ h ↦ h) x ω hparent a ha).1
  rw [killedChildRecords_renewal D K C hKC hCD x F ω a
    (a + domainSteps C (x + position ω a) (shift a ω)) hparent haeq rfl hentry,
    killedChildRecords_inside D K C hKC hCD (x + position ω a) hentry F (shift a ω) hf]
  apply congrArg (List.cons (F (x + position ω a)
    (killedPathWord C (x + position ω a) (shift a ω))))
  simp only [domainExitLocation, futureAt, position_add, ← add_assoc, shift_shift_path] <;> rfl

/-- A nonempty actual record event factors through the successful competing entrance. -/
theorem killedChildRecords_cons_iff_entrance (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) {R : Type*} (x : Site) (F : Site → PathWord → R)
    (r : R) (rs : List R) (ω : Sample) (hparent : domainExit D x ω ≠ ⊤) :
    killedChildRecords D K C x F ω = r :: rs ↔
      domainExitLocation (D \ K) x ω ∈ K ∧
        killedChildRecords D K C (domainExitLocation (D \ K) x ω) F
          (futureAt (domainExit (D \ K) x) ω) = r :: rs := by
  change killedChildRecords D K C x F ω = r :: rs ↔
    x + position ω (domainSteps (D \ K) x ω) ∈ K ∧
      killedChildRecords D K C (x + position ω (domainSteps (D \ K) x ω)) F
        (shift (domainSteps (D \ K) x ω) ω) = r :: rs
  by_cases hk : x + position ω (domainSteps (D \ K) x ω) ∈ K
  · rw [killedChildRecords_cut_at_entrance D K C hKC hCD x F ω hparent _ rfl hk]
    simp only [hk, true_and]
  · have hn : killedChildRecords D K C x F ω = [] :=
      (killedChildRecords_eq_nil_iff D K C x F ω).mpr
        ((killedChildIntervals_nil_iff_competing_exit D K C hKC hCD x ω hparent).mpr hk)
    simp [hn, hk]

/-- A nonempty actual list integrates its entrance-site probability against U. -/
theorem killedChildRecords_entrance_probability (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) {R : Type*} (x : Site) (F : Site → PathWord → R)
    (r : R) (rs : List R) :
    pathLaw {ω | killedChildRecords D K C x F ω = r :: rs} =
      ∫⁻ z, pathLaw {ω | killedChildRecords D K C z F ω = r :: rs}
        ∂competingEntranceLaw D K x := by
  rw [← competing_entrance_future_integral D K x
    (fun z ↦ {ω | killedChildRecords D K C z F ω = r :: rs})
    (fun z ↦ measurableSet_killedChildRecords_eq D K C z F (r :: rs))]
  apply measure_congr
  filter_upwards [domainExit_ne_top_ae D x] with ω hω
  exact propext (killedChildRecords_cons_iff_entrance D K C hKC hCD x F r rs ω hω)

/-- Exact U-S recursion for the probability of any specified nonempty ordered child list. -/
theorem killedChildRecords_cons_probability (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) {R : Type*} (x : Site) (F : Site → PathWord → R)
    (r : R) (rs : List R) :
    pathLaw {ω | killedChildRecords D K C x F ω = r :: rs} =
      ∫⁻ z, ∫⁻ ξ, pathLaw {ω | killedChildRecords D K C ξ F ω = rs}
        ∂recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r
        ∂competingEntranceLaw D K x := by
  rw [killedChildRecords_entrance_probability D K C hKC hCD x F r rs]
  apply lintegral_congr_ae
  filter_upwards [competingEntranceLaw_supported D K x] with z hz
  exact killedChildRecords_inside_cons_probability D K C hKC hCD z hz F r rs

end SRWTightness
