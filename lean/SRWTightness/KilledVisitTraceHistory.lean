import SRWTightness.VisitTraceHistory
import SRWTightness.VisitTraceLastTime
import SRWTightness.KilledVisitTraceSplit
import SRWTightness.ChildExitBounds

namespace SRWTightness

/-- A finite path starting in the observed set has a nonempty killed trace. -/
theorem killed_visit_trace_ne_nil (D K : Finset Site) (x : Site)
    (hKD : K ⊆ D) (hx : x ∈ K) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    killedVisitTrace D K x ω ≠ [] := by
  rw [killed_visit_trace_first_step D K x hKD hx ω hfin]
  simp

/-- A finite killed trace factors at its last visiting time into history and terminal escape. -/
theorem killed_visit_trace_history_iff (D K : Finset Site) (x : Site)
    (hKD : K ⊆ D) (hx : x ∈ K) (ξ : List Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) :
    killedVisitTrace D K x ω = ξ ↔ ∃ n, ω ∈ visitTraceHistoryEvent D K x ξ n ∧
      domainExit D (ξ.getLastD x) (shift n ω) <
        setHittingTime K (ξ.getLastD x) 1 (shift n ω) := by
  constructor
  · intro htrace
    have hne := killed_visit_trace_ne_nil D K x hKD hx ω hfin
    rw [killed_visit_trace_eq_range] at hne
    obtain ⟨n, hn, hmem, he⟩ :=
      visit_trace_range_last_time K x ω (domainSteps D x ω) hne
    have hprefix : visitTraceRange K x ω n ++ [x + position ω n] = ξ := by
      rw [← htrace, killed_visit_trace_eq_range, he, visit_trace_range_succ, if_pos hmem]
    have hhistory : ω ∈ visitTraceHistoryEvent D K x ξ n := by
      apply (visit_trace_history_event_iff D K x ξ n ω).mpr
      exact ⟨fun i hi ↦ position_before_domainSteps_mem D x ω hfin i (hi.trans_lt hn),
        hmem, hprefix⟩
    refine ⟨n, hhistory, ?_⟩
    have hf := (shifted_subdomain_exit_bounds D D (fun _ h ↦ h) x ω hfin n hn.le).1
    rw [← visit_trace_history_last D K x ξ n ω hhistory]
    apply (killed_visit_trace_singleton_iff D K _ hKD hmem _ hf).mp
    have hs := killed_visit_trace_split D K x ω hfin n hn.le
    rw [htrace, ← hprefix] at hs
    exact (List.append_cancel_left hs).symm
  · rintro ⟨n, hhistory, hescape⟩
    have he := (visit_trace_history_event_iff D K x ξ n ω).mp hhistory
    have hn := visit_trace_history_before_exit D K x ξ n ω hfin hhistory
    have hf := (shifted_subdomain_exit_bounds D D (fun _ h ↦ h) x ω hfin n hn.le).1
    rw [← visit_trace_history_last D K x ξ n ω hhistory] at hescape
    have hs := (killed_visit_trace_singleton_iff D K _ hKD he.2.1 _ hf).mpr hescape
    rw [killed_visit_trace_split D K x ω hfin n hn.le, hs]
    exact he.2.2

/-- Shifting before killing preserves the actual exit location. -/
theorem domain_exit_location_shift_before (D : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) (n : ℕ) (hn : n ≤ domainSteps D x ω) :
    domainExitLocation D (x + position ω n) (shift n ω) = domainExitLocation D x ω := by
  simp only [domainExitLocation, domainSteps_shift_before_exit D x ω hfin n hn]
  rw [add_assoc, ← position_add, Nat.add_sub_of_le hn]

/-- The history factorization retains any prescribed final exit atom. -/
theorem killed_visit_trace_exit_history_iff (D K : Finset Site) (x e : Site)
    (hKD : K ⊆ D) (hx : x ∈ K) (ξ : List Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) :
    (killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e) ↔
      ∃ n, ω ∈ visitTraceHistoryEvent D K x ξ n ∧
        (domainExit D (ξ.getLastD x) (shift n ω) <
          setHittingTime K (ξ.getLastD x) 1 (shift n ω) ∧
          domainExitLocation D (ξ.getLastD x) (shift n ω) = e) := by
  rw [killed_visit_trace_history_iff D K x hKD hx ξ ω hfin]
  constructor
  · rintro ⟨⟨n, hh, hb⟩, he⟩
    refine ⟨n, hh, hb, ?_⟩
    rw [← visit_trace_history_last D K x ξ n ω hh,
      domain_exit_location_shift_before D x ω hfin n
        (visit_trace_history_before_exit D K x ξ n ω hfin hh).le]
    exact he
  · rintro ⟨n, hh, hb, he⟩
    refine ⟨⟨n, hh, hb⟩, ?_⟩
    rw [← visit_trace_history_last D K x ξ n ω hh,
      domain_exit_location_shift_before D x ω hfin n
        (visit_trace_history_before_exit D K x ξ n ω hfin hh).le] at he
    exact he

end SRWTightness
