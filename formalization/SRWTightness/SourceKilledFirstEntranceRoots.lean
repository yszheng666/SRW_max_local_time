import SRWTightness.SourceTerminalFirstEntranceRoots
import SRWTightness.ActualTerminalWordVisits

namespace SRWTightness

/-- On the original killed path, terminal first-entry marks retain every complete short root. -/
theorem source_killed_firstEntrance_root_count_sum (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ : ℕ) (b : Site) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (k n : ℕ) (hn : k + n + 1 ≤ ℓ) (D O L E : Finset Site)
    (hCD : sourceExitDomain m r ℓ b k ⊆ D) (hLE : L ⊆ E) (hLO : L ⊆ O)
    (hL : L ⊆ sourceEntranceDomain m r ℓ b (k + n))
    (hE : E ⊆ sourceExitDomain m r ℓ b (k + n))
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    ((actualTerminalWordRecords (sourceExcursionLevels m r ℓ b k (n + 1)) D x ω).map
      (fun p ↦ wordMarkRootCount L E (firstEntranceWordOfWord
        (sourceExitDomain m r ℓ b (k + n)) O p.1 p.2))).sum =
          (killedChildIntervals D L E x ω).length :=
  source_terminal_firstEntrance_root_count_sum hF m r ℓ b hr hm k n hn O L E hLE hLO
    hL hE x (killedPathWord D x ω)
    (killedPathWord_endpoint_outside_child D _ hCD x ω hfin)

end SRWTightness
