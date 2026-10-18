import SRWTightness.ChildZeroRecord
import SRWTightness.ChildExitBounds

namespace SRWTightness

/-- The competing exit lands in K exactly when the original killed path visits K. -/
theorem competing_exit_mem_iff_occupation_pos (D K : Finset Site) (hKD : K ⊆ D)
    (x : Site) (ω : Sample) (hparent : domainExit D x ω ≠ ⊤) :
    x + position ω (domainSteps (D \ K) x ω) ∈ K ↔ 0 < setOccupation D K x ω := by
  obtain ⟨hc, hca⟩ := subdomain_exit_bounds D (D \ K) Finset.sdiff_subset x ω hparent
  constructor
  · intro hk
    have ha : domainSteps (D \ K) x ω < domainSteps D x ω := by
      by_contra hn
      have he : domainSteps (D \ K) x ω = domainSteps D x ω := by omega
      exact position_domain_exit_not_mem D x ω hparent (he ▸ hKD hk)
    exact (setOccupation_pos_iff D K x ω).mpr ⟨_, ha, hk⟩
  · intro hp
    obtain ⟨j, hj, hk⟩ := (setOccupation_pos_iff D K x ω).mp hp
    have he : domainExit (D \ K) x ω ≤ j :=
      (domainExit_le_iff (D \ K) x ω j).mpr
        ⟨j, le_rfl, fun h ↦ (Finset.mem_sdiff.mp h).2 hk⟩
    rw [← coe_domainSteps (D \ K) x ω hc] at he
    have ha := lt_of_le_of_lt (WithTop.coe_le_coe.mp he) hj
    have hD := position_before_domainSteps_mem D x ω hparent _ ha
    by_contra hn
    exact position_domain_exit_not_mem (D \ K) x ω hc (Finset.mem_sdiff.mpr ⟨hD, hn⟩)

/-- No child is produced precisely on the competing outer-exit branch. -/
theorem killedChildIntervals_nil_iff_competing_exit (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) (ω : Sample) (hparent : domainExit D x ω ≠ ⊤) :
    killedChildIntervals D K C x ω = [] ↔
      x + position ω (domainSteps (D \ K) x ω) ∉ K := by
  rw [killedChildIntervals_eq_nil_iff D K C hKC hCD x ω hparent]
  have hh := competing_exit_mem_iff_occupation_pos D K (fun y hy ↦ hCD (hKC hy)) x ω hparent
  constructor
  · intro hz hk
    have hp := hh.mp hk
    omega
  · intro hn
    by_contra hz
    exact hn (hh.mpr (by omega))

/-- Complete actual-path recursion: either outer escape, or one child followed by renewal. -/
theorem killedChildIntervals_branching (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) (ω : Sample) (a b : ℕ)
    (hparent : domainExit D x ω ≠ ⊤)
    (haeq : a = domainSteps (D \ K) x ω)
    (hbeq : b = a + domainSteps C (x + position ω a) (shift a ω)) :
    killedChildIntervals D K C x ω =
      if x + position ω a ∈ K then
        (a, b) :: (killedChildIntervals D K C (x + position ω b) (shift b ω)).map
          (fun q ↦ (b + q.1, b + q.2))
      else [] := by
  split_ifs with hk
  · exact killedChildIntervals_nested_renewal D K C hKC hCD x ω a b hparent haeq hbeq hk
  · apply (killedChildIntervals_nil_iff_competing_exit D K C hKC hCD x ω hparent).mpr
    simpa only [← haeq] using hk

end SRWTightness
