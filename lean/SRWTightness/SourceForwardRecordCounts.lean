import SRWTightness.SourceRecordLevelPopulation

namespace SRWTightness

/-- Number of actual level-i segments extracted from an exterior path beginning at level k. -/
noncomputable def sourceForwardRecordCount (m r : ℝ) (ℓ k i : ℕ) (b : Site)
    (D : Finset Site) (x : Site) (ω : Sample) : ℕ :=
  (actualTerminalWordRecords (sourceExcursionLevels m r ℓ b k (i - k + 1)) D x ω).length

/-- Forward manuscript generations correspond to reversed finite-tree populations. -/
theorem source_forward_record_population {M : Type*} (m r : ℝ) (ℓ k i : ℕ)
    (hki : k ≤ i) (hi : i < ℓ) (b : Site) (D : Finset Site) (x : Site)
    (F : Site → PathWord → M) (ω : Sample) :
    finiteRecordLevelPopulation (ℓ - k)
      (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        F (ℓ - k) x (killedPathWord D x ω)) (ℓ - (i + 1)) =
      sourceForwardRecordCount m r ℓ k i b D x ω := by
  rw [source_record_level_population m r ℓ k (ℓ - (i + 1)) (by omega) (by omega)]
  have hidx : ℓ - k - (ℓ - (i + 1)) = i - k + 1 := by omega
  rw [hidx]
  rfl

/-- At the terminal generation the forward count is exactly the existing terminal record count. -/
theorem source_forward_terminal_count (m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ)
    (b : Site) (D : Finset Site) (x : Site) (ω : Sample) :
    sourceForwardRecordCount m r ℓ k (ℓ - 1) b D x ω =
      (sourceTerminalRecords m r ℓ k b D x ω).length := by
  unfold sourceForwardRecordCount sourceTerminalRecords
  have hidx : ℓ - 1 - k + 1 = ℓ - k := by omega
  rw [hidx]

end SRWTightness
