import SRWTightness.SourceActualRootList
import SRWTightness.SourceRecordTreeLeaves

namespace SRWTightness

/-- The full ordered leaf list of all level-k roots is the original terminal extraction starting at k. -/
theorem source_forest_leaves {M : Type*} (m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ)
    (b : Site) (D : Finset Site) (x : Site) (F : Site → PathWord → M) (ω : Sample) :
    (killedChildRecords D (sourceEntranceDomain m r ℓ b k) (sourceExitDomain m r ℓ b k) x
      (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        F (ℓ - (k + 1))) ω).flatMap (finiteRecordLeaves (ℓ - (k + 1))) =
      (sourceTerminalRecords m r ℓ k b D x ω).map (fun p ↦ F p.1 p.2) := by
  have hl := source_record_tree_leaves m r ℓ k hk.le b D x F ω
  have hn : ℓ - k = ℓ - (k + 1) + 1 := by omega
  rw [hn, finiteRecordLeaves, source_actual_root_list m r ℓ k hk] at hl
  exact hl

end SRWTightness
