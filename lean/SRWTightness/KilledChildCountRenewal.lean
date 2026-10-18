import SRWTightness.ActualRecordKernel

open MeasureTheory

namespace SRWTightness

/-- The tail event for the actual complete child count is measurable. -/
theorem measurableSet_killedChildIntervals_length_ge (D K C : Finset Site) (x : Site)
    (n : ℕ) : MeasurableSet {ω | n ≤ (killedChildIntervals D K C x ω).length} :=
  (measurable_killedPathWord D x) (Set.to_countable
    {w : PathWord | n ≤ (wordChildIntervals K C x w).length}).measurableSet

/-- A positive child-count tail factors through the first successful entrance. -/
theorem killedChildIntervals_length_ge_entrance (D K C : Finset Site)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (x : Site) (n : ℕ) :
    pathLaw.real {ω | n + 1 ≤ (killedChildIntervals D K C x ω).length} =
      ∫ z, pathLaw.real {ω | n + 1 ≤ (killedChildIntervals D K C z ω).length}
        ∂competingEntranceLaw D K x := by
  let t : Site → Set Sample := fun z ↦
    {ω | n + 1 ≤ (killedChildIntervals D K C z ω).length}
  have he : pathLaw (t x) = ∫⁻ z, pathLaw (t z) ∂competingEntranceLaw D K x := by
    rw [← competing_entrance_future_integral D K x t
      (fun z ↦ measurableSet_killedChildIntervals_length_ge D K C z (n + 1))]
    apply measure_congr
    filter_upwards [domainExit_ne_top_ae D x] with ω hω
    change (n + 1 ≤ (killedChildIntervals D K C x ω).length) =
      (domainExitLocation (D \ K) x ω ∈ K ∧
        n + 1 ≤ (killedChildIntervals D K C (domainExitLocation (D \ K) x ω)
          (futureAt (domainExit (D \ K) x) ω)).length)
    apply propext
    by_cases hk : domainExitLocation (D \ K) x ω ∈ K
    · have hc := congrArg List.length (killedChildRecords_cut_at_entrance D K C hKC hCD x
        (fun _ _ ↦ ()) ω hω (domainSteps (D \ K) x ω) rfl hk)
      simp only [killedChildRecords_length] at hc
      change (killedChildIntervals D K C x ω).length =
        (killedChildIntervals D K C (domainExitLocation (D \ K) x ω)
          (futureAt (domainExit (D \ K) x) ω)).length at hc
      simp only [hk, true_and, hc]
    · have hn := (killedChildIntervals_nil_iff_competing_exit D K C hKC hCD x ω hω).mpr hk
      simp [hn, hk]
  have hi := integral_toReal (μ := competingEntranceLaw D K x)
    (f := fun z ↦ pathLaw (t z)) (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall (fun z ↦ measure_lt_top pathLaw (t z)))
  exact (congrArg ENNReal.toReal he).trans hi.symm

/-- From an inner entrance, the first child is completed and the count renews at its exit. -/
theorem killedChildIntervals_length_ge_inside (D K C : Finset Site)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (x : Site) (hx : x ∈ K) (n : ℕ) :
    pathLaw.real {ω | n + 1 ≤ (killedChildIntervals D K C x ω).length} =
      ∫ ξ, pathLaw.real {ω | n ≤ (killedChildIntervals D K C ξ ω).length}
        ∂recordExitSlice C x (fun _ ↦ ()) () := by
  let t : Site → Set Sample := fun ξ ↦
    {ω | n ≤ (killedChildIntervals D K C ξ ω).length}
  have he : pathLaw {ω | n + 1 ≤ (killedChildIntervals D K C x ω).length} =
      ∫⁻ ξ, pathLaw (t ξ) ∂recordExitSlice C x (fun _ ↦ ()) () := by
    rw [← killed_record_future_exit_integral C x (fun _ ↦ ()) () t
      (fun ξ ↦ measurableSet_killedChildIntervals_length_ge D K C ξ n)]
    apply measure_congr
    filter_upwards [domainExit_ne_top_ae D x] with ω hω
    have hc := congrArg List.length (killedChildRecords_inside D K C hKC hCD x hx
      (fun _ _ ↦ ()) ω hω)
    simp only [List.length_cons, killedChildRecords_length] at hc
    change (n + 1 ≤ (killedChildIntervals D K C x ω).length) =
      (() = () ∧ n ≤ (killedChildIntervals D K C (domainExitLocation C x ω)
        (futureAt (domainExit C x) ω)).length)
    rw [hc]
    simp only [Nat.add_le_add_iff_right, true_and]
  have hi := integral_toReal (μ := recordExitSlice C x (fun _ ↦ ()) ())
    (f := fun ξ ↦ pathLaw (t ξ)) (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall (fun ξ ↦ measure_lt_top pathLaw (t ξ)))
  exact (congrArg ENNReal.toReal he).trans hi.symm

end SRWTightness
