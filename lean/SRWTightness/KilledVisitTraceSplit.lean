import SRWTightness.VisitTraceRange
import SRWTightness.DomainStepsShift
import SRWTightness.ReturnTime

namespace SRWTightness

/-- Before killing, the chronological trace splits into its past and restarted future. -/
theorem killed_visit_trace_split (D K : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) (n : ℕ) (hn : n ≤ domainSteps D x ω) :
    killedVisitTrace D K x ω = visitTraceRange K x ω n ++
      killedVisitTrace D K (x + position ω n) (shift n ω) := by
  rw [killed_visit_trace_eq_range, killed_visit_trace_eq_range,
    domainSteps_shift_before_exit D x ω hfin n hn,
    ← visit_trace_range_add, Nat.add_sub_of_le hn]

/-- An empty killed trace means that the observed set has zero occupation. -/
theorem killed_visit_trace_nil_iff (D K : Finset Site) (x : Site) (ω : Sample) :
    killedVisitTrace D K x ω = [] ↔ setOccupation D K x ω = 0 := by
  rw [killed_visit_trace_eq_range, visit_trace_range_eq_nil_iff]
  have h := setOccupation_pos_iff D K x ω
  constructor
  · intro hn
    by_contra hz
    obtain ⟨i, hi, hm⟩ := h.mp (Nat.pos_of_ne_zero hz)
    exact hn i hi hm
  · intro hz i hi hm
    have := h.mpr ⟨i, hi, hm⟩
    omega

/-- A path starting inside the domain has at least one position before its finite exit. -/
theorem domain_steps_pos_of_mem (D : Finset Site) (x : Site) (hx : x ∈ D)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) : 0 < domainSteps D x ω := by
  by_contra h
  have hz : domainSteps D x ω = 0 := by omega
  have hout := position_domain_exit_not_mem D x ω hfin
  have hnot : x ∉ D := by simpa [hz] using hout
  exact hnot hx

/-- Starting in the observed set records the initial point and then the future trace. -/
theorem killed_visit_trace_first_step (D K : Finset Site) (x : Site)
    (hKD : K ⊆ D) (hx : x ∈ K) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    killedVisitTrace D K x ω = [x] ++
      killedVisitTrace D K (x + step (ω 0)) (shift 1 ω) := by
  rw [killed_visit_trace_split D K x ω hfin 1
    (domain_steps_pos_of_mem D x (hKD hx) ω hfin)]
  have hp : position ω 1 = step (ω 0) := by
    change (0 : Site) + step (ω 0) = _
    rw [zero_add]
  rw [hp]
  change (List.filter (fun z ↦ decide (z ∈ K)) [x + (0 : Site)]) ++ _ = _
  simp [hx]

/-- A singleton trace is precisely escape before a positive return to the observation set. -/
theorem killed_visit_trace_singleton_iff (D K : Finset Site) (x : Site)
    (hKD : K ⊆ D) (hx : x ∈ K) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    killedVisitTrace D K x ω = [x] ↔
      domainExit D x ω < setHittingTime K x 1 ω := by
  have hf : domainExit D (x + step (ω 0)) (shift 1 ω) ≠ ⊤ := by
    rw [domainExit_first_step D x (hKD hx) ω] at hfin
    exact (WithTop.add_ne_top.mp hfin).2
  rw [killed_visit_trace_first_step D K x hKD hx ω hfin,
    exit_before_return_first_step D K x (hKD hx) ω,
    exit_lt_setHittingTime_iff D K hKD _ _ hf]
  simpa using killed_visit_trace_nil_iff D K (x + step (ω 0)) (shift 1 ω)

end SRWTightness
