import SRWTightness.GrowingRecordDomains
import SRWTightness.SourceRecordTreeLeaves

namespace SRWTightness

/-- Reversing the source level index gives the outward geometric radius. -/
theorem sourceRecordRadius_reverse (m : ℝ) (ℓ n : ℕ) (hn : n ≤ ℓ) :
    sourceRecordRadius m ℓ (ℓ - n) = growingRecordRadius m n := by
  unfold sourceRecordRadius growingRecordRadius
  rw [Nat.cast_sub hn]
  congr 2
  ring

/-- The reverse source entrance domain is the geometric entrance domain on valid levels. -/
theorem source_tree_entrance_growing (m r : ℝ) (ℓ : ℕ) (b : Site) (n : ℕ) (hn : n < ℓ) :
    sourceTreeEntrance m r ℓ b n = growingRecordEntrance b m (sourceRecordBuffer r) n := by
  have hi : ℓ - (n + 1) + 1 = ℓ - n := by omega
  unfold sourceTreeEntrance sourceEntranceDomain
  rw [hi, sourceRecordRadius_reverse m ℓ n hn.le]
  rfl

/-- The reverse source killing domain is the geometric killing domain on valid levels. -/
theorem source_tree_exit_growing (m r : ℝ) (ℓ : ℕ) (b : Site) (n : ℕ) (hn : n < ℓ) :
    sourceTreeExit m r ℓ b n = growingRecordExit b m (sourceRecordBuffer r) n := by
  unfold sourceTreeExit sourceExitDomain
  rw [sourceRecordRadius_reverse m ℓ (n + 1) (by omega), growingRecordRadius_succ]
  rfl

/-- The actual source tree is the geometrically indexed actual tree throughout its finite depth. -/
theorem source_actual_tree_growing {M : Type*} (m r : ℝ) (ℓ : ℕ) (b : Site)
    (F : Site → PathWord → M) (n : ℕ) : n ≤ ℓ →
    actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b) F n =
      actualFiniteWordRecord (growingRecordEntrance b m (sourceRecordBuffer r))
        (growingRecordExit b m (sourceRecordBuffer r)) F n := by
  induction n with
  | zero => intro hn; rfl
  | succ n ih =>
    intro hn
    simp only [actualFiniteWordRecord, source_tree_entrance_growing m r ℓ b n (by omega),
      source_tree_exit_growing m r ℓ b n (by omega), ih (by omega)]

end SRWTightness
