import SRWTightness.SourceActualRootList
import SRWTightness.WordOccupationMark
import SRWTightness.SourceRecordTreeLeaves

namespace SRWTightness

/-- A single actual root contains all terminal marks contributing to the original local time. -/
theorem source_single_root_mark_visits (m ρ : ℝ) (n : ℕ) (b : Site)
    (D K : Finset Site) (x : Site) (hρ : 0 ≤ ρ)
    (hm : sourceRecordBuffer ρ + 2 ≤ m)
    (hK : K ⊆ translateFinset b (diskFinset (m - sourceRecordBuffer ρ - 2)))
    (hroot : sourceExitDomain m ρ (n + 1) b 0 ⊆ D)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤)
    (r : FiniteExcursionRecord (Mark K) n)
    (hr : killedChildRecords D (sourceEntranceDomain m ρ (n + 1) b 0)
      (sourceExitDomain m ρ (n + 1) b 0) x
      (actualFiniteWordRecord (sourceTreeEntrance m ρ (n + 1) b)
        (sourceTreeExit m ρ (n + 1) b) (wordOccupationMark K) n) ω = [r]) (y : K) :
    ((finiteRecordLeaves n r).map (fun v ↦ v y)).sum = domainLocalTime D x y ω := by
  have hlist := source_actual_root_list m ρ (n + 1) 0 (by omega) b
    (wordOccupationMark K) x (killedPathWord D x ω)
  change actualFiniteWordRecord (sourceTreeEntrance m ρ (n + 1) b)
    (sourceTreeExit m ρ (n + 1) b) (wordOccupationMark K) (n + 1) x
    (killedPathWord D x ω) = killedChildRecords D
      (sourceEntranceDomain m ρ (n + 1) b 0) (sourceExitDomain m ρ (n + 1) b 0) x
      (actualFiniteWordRecord (sourceTreeEntrance m ρ (n + 1) b)
        (sourceTreeExit m ρ (n + 1) b) (wordOccupationMark K) n) ω at hlist
  rw [hr] at hlist
  have hleaves := source_record_tree_leaves m ρ (n + 1) 0 (by omega) b D x
    (wordOccupationMark K) ω
  simp only [Nat.sub_zero, hlist, finiteRecordLeaves, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] at hleaves
  have hsum := congrArg (fun l : List (Mark K) ↦ (l.map (fun v ↦ v y)).sum) hleaves
  rw [List.map_map] at hsum
  have hv := source_terminal_visit_identity m ρ (n + 1) 0 (by omega) b D K x
    hρ hm hK hroot ω hfin y y.property
  exact hsum.trans hv.symm

end SRWTightness
