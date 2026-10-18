import SRWTightness.ChildFirstExit

namespace SRWTightness

/-- Before the first entrance, the scanner consumes the pre without opening a child. -/
theorem scanChildIntervals_skip_prefix (K C : Finset Site) (x : Site) (ω : Sample)
    (pre ts : List ℕ) (hprefix : ∀ i ∈ pre, x + position ω i ∉ K) :
    scanChildIntervals K C x ω none (pre ++ ts) =
      scanChildIntervals K C x ω none ts := by
  induction pre with
  | nil => rfl
  | cons i pre ih =>
    have hi := hprefix i List.mem_cons_self
    simpa [scanChildIntervals, hi] using
      ih (fun j hj ↦ hprefix j (List.mem_cons_of_mem i hj))

/-- A competing exit landing in the entrance set is the first opened child. -/
theorem scanChildIntervals_competing_entrance (D K C : Finset Site) (x : Site)
    (ω : Sample) (pre ts : List ℕ)
    (hfin : domainExit (D \ K) x ω ≠ ⊤)
    (hprefix : ∀ i ∈ pre, i < domainSteps (D \ K) x ω)
    (hentry : x + position ω (domainSteps (D \ K) x ω) ∈ K) :
    scanChildIntervals K C x ω none
        (pre ++ domainSteps (D \ K) x ω :: ts) =
      scanChildIntervals K C x ω (some (domainSteps (D \ K) x ω)) ts := by
  rw [scanChildIntervals_skip_prefix K C x ω pre _]
  · simp [scanChildIntervals, hentry]
  · intro i hi
    exact (Finset.mem_sdiff.mp
      (position_before_domainSteps_mem (D \ K) x ω hfin i (hprefix i hi))).2

/-- The scanner's first child has the actual competing entrance and shifted domain exit. -/
theorem scanChildIntervals_competing_child (D K C : Finset Site) (x : Site)
    (ω : Sample) (pre ts : List ℕ) (ht : ts.Pairwise (· < ·))
    (hfin : domainExit (D \ K) x ω ≠ ⊤)
    (hprefix : ∀ i ∈ pre, i < domainSteps (D \ K) x ω)
    (hentry : x + position ω (domainSteps (D \ K) x ω) ∈ K)
    (hafter : ∀ i ∈ ts, domainSteps (D \ K) x ω ≤ i)
    (hchild : domainExit C (x + position ω (domainSteps (D \ K) x ω))
      (shift (domainSteps (D \ K) x ω) ω) ≠ ⊤)
    (hend : domainSteps (D \ K) x ω +
      domainSteps C (x + position ω (domainSteps (D \ K) x ω))
        (shift (domainSteps (D \ K) x ω) ω) ∈ ts) :
    ∃ rs, scanChildIntervals K C x ω none
        (pre ++ domainSteps (D \ K) x ω :: ts) =
      (domainSteps (D \ K) x ω, domainSteps (D \ K) x ω +
        domainSteps C (x + position ω (domainSteps (D \ K) x ω))
          (shift (domainSteps (D \ K) x ω) ω)) :: rs := by
  rw [scanChildIntervals_skip_prefix K C x ω pre _]
  · exact scanChildIntervals_entry_domain_exit K C x ω ts ht _ hentry hafter hchild hend
  · intro i hi
    exact (Finset.mem_sdiff.mp
      (position_before_domainSteps_mem (D \ K) x ω hfin i (hprefix i hi))).2

end SRWTightness
