import SRWTightness.ChildExitRenewal
import SRWTightness.DomainStepsShift

namespace SRWTightness

/-- The actual child list renews as the same killed-path extractor at the first child exit. -/
theorem killedChildIntervals_renewal (D K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (a b : ℕ)
    (hparent : domainExit D x ω ≠ ⊤)
    (haeq : a = domainSteps (D \ K) x ω)
    (hbeq : b = a + domainSteps C (x + position ω a) (shift a ω))
    (hfin : domainExit (D \ K) x ω ≠ ⊤)
    (hentry : x + position ω a ∈ K)
    (hchild : domainExit C (x + position ω a) (shift a ω) ≠ ⊤)
    (hb : b ≤ domainSteps D x ω) :
    killedChildIntervals D K C x ω =
      (a, b) :: (killedChildIntervals D K C (x + position ω b) (shift b ω)).map
        (fun q ↦ (b + q.1, b + q.2)) := by
  rw [killedChildIntervals_restart_at_exit D K C hKC x ω a b haeq hbeq
    hfin hentry hchild hb, killedChildIntervals_eq_scan,
    domainSteps_shift_before_exit D x ω hparent b hb]

end SRWTightness
