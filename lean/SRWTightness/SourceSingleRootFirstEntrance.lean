import SRWTightness.SourceTreeFirstEntranceRoots
import SRWTightness.SourceActualRootList

namespace SRWTightness

/-- A selected single source root retains all short roots in its first-entry leaf marks. -/
theorem source_single_root_firstEntrance_sum (hF : TwoLevelWordFlatteningInput)
    (m ρ : ℝ) (n : ℕ) (b : Site) (D O L E : Finset Site) (x : Site)
    (hρ : 0 ≤ ρ) (hm : sourceRecordBuffer ρ + 2 ≤ m)
    (hroot : sourceExitDomain m ρ (n + 1) b 0 ⊆ D)
    (hLE : L ⊆ E) (hLO : L ⊆ O)
    (hL : L ⊆ sourceEntranceDomain m ρ (n + 1) b n)
    (hE : E ⊆ sourceExitDomain m ρ (n + 1) b n)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤)
    (r : FiniteExcursionRecord WordMark n)
    (hr : killedChildRecords D (sourceEntranceDomain m ρ (n + 1) b 0)
      (sourceExitDomain m ρ (n + 1) b 0) x
      (actualFiniteWordRecord (sourceTreeEntrance m ρ (n + 1) b)
        (sourceTreeExit m ρ (n + 1) b)
        (firstEntranceWordOfWord (sourceExitDomain m ρ (n + 1) b n) O) n) ω = [r]) :
    ((finiteRecordLeaves n r).map (wordMarkRootCount L E)).sum =
      (killedChildIntervals D L E x ω).length := by
  let F := firstEntranceWordOfWord (sourceExitDomain m ρ (n + 1) b n) O
  have hlist := source_actual_root_list m ρ (n + 1) 0 (by omega) b
    F x (killedPathWord D x ω)
  change actualFiniteWordRecord (sourceTreeEntrance m ρ (n + 1) b)
    (sourceTreeExit m ρ (n + 1) b) F (n + 1) x
    (killedPathWord D x ω) = killedChildRecords D
      (sourceEntranceDomain m ρ (n + 1) b 0) (sourceExitDomain m ρ (n + 1) b 0) x
      (actualFiniteWordRecord (sourceTreeEntrance m ρ (n + 1) b)
        (sourceTreeExit m ρ (n + 1) b) F n) ω at hlist
  rw [hr] at hlist
  have hh := source_tree_firstEntrance_root_sum hF m ρ (n + 1) 0 (by omega) b D O L E
    hρ hm hroot hLE hLO (by simpa using hL) (by simpa using hE) x ω hfin
  change ((finiteRecordLeaves (n + 1)
    (actualFiniteWordRecord (sourceTreeEntrance m ρ (n + 1) b)
      (sourceTreeExit m ρ (n + 1) b) F (n + 1) x
      (killedPathWord D x ω))).map (wordMarkRootCount L E)).sum = _ at hh
  rw [hlist] at hh
  simpa only [finiteRecordLeaves, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hh

end SRWTightness
