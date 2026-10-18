import SRWTightness.SourceForwardRecordCounts

namespace SRWTightness

/-- The outer extraction is a list of actual roots, each carrying one fewer tree level. -/
theorem source_actual_root_list {M : Type*} (m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ)
    (b : Site) (F : Site → PathWord → M) (x : Site) (w : PathWord) :
    actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        F (ℓ - (k + 1) + 1) x w =
      wordChildRecords (sourceEntranceDomain m r ℓ b k) (sourceExitDomain m r ℓ b k) x
        (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
          F (ℓ - (k + 1))) w := by
  have hidx : ℓ - (ℓ - (k + 1) + 1) = k := by omega
  simp only [actualFiniteWordRecord, sourceTreeEntrance, sourceTreeExit, hidx]

/-- The forward root count counts precisely the chronological complete root intervals. -/
theorem source_forward_root_count (m r : ℝ) (ℓ k : ℕ) (b : Site)
    (D : Finset Site) (x : Site) (ω : Sample) :
    sourceForwardRecordCount m r ℓ k k b D x ω =
      (wordChildIntervals (sourceEntranceDomain m r ℓ b k) (sourceExitDomain m r ℓ b k)
        x (killedPathWord D x ω)).length := by
  simp [sourceForwardRecordCount, actualTerminalWordRecords, sourceExcursionLevels,
    terminalWordRecords, List.length_flatMap]

/-- Observing each root's internal tree preserves the actual root count. -/
theorem source_actual_root_list_length {M : Type*} (m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ)
    (b : Site) (D : Finset Site) (x : Site) (F : Site → PathWord → M) (ω : Sample) :
    (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
      F (ℓ - (k + 1) + 1) x (killedPathWord D x ω)).length =
        sourceForwardRecordCount m r ℓ k k b D x ω := by
  rw [source_actual_root_list m r ℓ k hk]
  rw [source_forward_root_count]
  simp only [wordChildRecords, List.length_map]

end SRWTightness
