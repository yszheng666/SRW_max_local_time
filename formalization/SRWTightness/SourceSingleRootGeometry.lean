import SRWTightness.SourceGrowingRecordIdentity

namespace SRWTightness

/-- The entrance scale of a source root is the outward radius at its remaining tree depth. -/
theorem source_single_root_radius (m : ℝ) (ℓ k : ℕ) (hk : k < ℓ) :
    sourceRecordRadius m ℓ (k + 1) = growingRecordRadius m (ℓ - (k + 1)) := by
  have hidx : ℓ - (ℓ - (k + 1)) = k + 1 := by omega
  simpa only [hidx] using
    sourceRecordRadius_reverse m ℓ (ℓ - (k + 1)) (by omega)

/-- The killing domain of one source root is exactly the geometric tree killing domain. -/
theorem source_single_root_exit (m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ) (b : Site) :
    sourceExitDomain m r ℓ b k =
      growingRecordExit b m (sourceRecordBuffer r) (ℓ - (k + 1)) := by
  have hidx : ℓ - (ℓ - (k + 1) + 1) = k := by omega
  simpa only [sourceTreeExit, hidx] using
    source_tree_exit_growing m r ℓ b (ℓ - (k + 1)) (by omega)

/-- The complete internal record of one actual source root is the geometric tree record. -/
theorem source_single_root_record {M : Type*} (m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ)
    (b : Site) (F : Site → PathWord → M) (x : Site) (ω : Sample) :
    actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        F (ℓ - (k + 1)) x (killedPathWord (sourceExitDomain m r ℓ b k) x ω) =
      actualFiniteWordRecord (growingRecordEntrance b m (sourceRecordBuffer r))
        (growingRecordExit b m (sourceRecordBuffer r)) F (ℓ - (k + 1)) x
        (killedPathWord (growingRecordExit b m (sourceRecordBuffer r) (ℓ - (k + 1))) x ω) := by
  rw [source_actual_tree_growing m r ℓ b F _ (by omega), source_single_root_exit m r ℓ k hk]

end SRWTightness
