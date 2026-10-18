import SRWTightness.SourceActualRootList
import SRWTightness.WordOccupationMark

namespace SRWTightness

/-- Summing every projected terminal mark over all actual roots recovers the killed local time. -/
theorem source_forest_mark_visits (m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ)
    (b : Site) (D K : Finset Site) (x : Site) (hr : 0 ≤ r)
    (hm : sourceRecordBuffer r + 2 ≤ m)
    (hK : K ⊆ translateFinset b (diskFinset (m - sourceRecordBuffer r - 2)))
    (hroot : sourceExitDomain m r ℓ b k ⊆ D)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (y : K) :
    let n := ℓ - (k + 1)
    let rs := killedChildRecords D (sourceEntranceDomain m r ℓ b k)
      (sourceExitDomain m r ℓ b k) x
      (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        (wordOccupationMark K) n) ω
    ((rs.flatMap (finiteRecordLeaves n)).map (fun v ↦ v y)).sum =
      domainLocalTime D x y ω := by
  dsimp only
  have hleaves := source_record_tree_leaves m r ℓ k hk.le b D x
    (wordOccupationMark K) ω
  have hdepth : ℓ - k = ℓ - (k + 1) + 1 := by omega
  rw [hdepth, source_actual_root_list m r ℓ k hk] at hleaves
  have hsum := congrArg (fun l : List (Mark K) ↦ (l.map (fun v ↦ v y)).sum) hleaves
  rw [List.map_map] at hsum
  have hv := source_terminal_visit_identity m r ℓ k hk b D K x
    hr hm hK hroot ω hfin y y.property
  exact hsum.trans hv.symm

end SRWTightness
