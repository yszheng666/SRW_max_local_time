import SRWTightness.ChildIntervalCompletion
import SRWTightness.SetHitting

namespace SRWTightness

/-- A completed pending interval covers every earlier time after its entrance. -/
theorem scanChildIntervals_pending_covers (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (a j : ℕ) (ha : a ≤ j) (ht : ∀ i ∈ ts, j < i)
    (hexit : ∃ i ∈ ts, x + position ω i ∉ C) :
    ∃ q ∈ scanChildIntervals K C x ω (some a) ts, q.1 ≤ j ∧ j < q.2 := by
  obtain ⟨q, hq, hstart⟩ := scanChildIntervals_pending_completed K C x ω ts a hexit
  have hend := (scanChildIntervals_endpoint_times K C x ω ts (some a) q hq).2
  exact ⟨q, hq, hstart.le.trans ha, ht q.2 hend⟩

/-- The actual parent exit is an available child-domain exit when the child domain is nested. -/
theorem killedPathWord_endpoint_outside_child (D C : Finset Site) (hCD : C ⊆ D)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    x + position (wordPath (killedPathWord D x ω)) (killedPathWord D x ω).length ∉ C := by
  rw [killedPathWord_exitLocation]
  exact fun hc ↦ position_domain_exit_not_mem D x ω hfin (hCD hc)

end SRWTightness
