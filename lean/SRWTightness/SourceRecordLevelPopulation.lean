import SRWTightness.ActualRecordLevelPopulation

namespace SRWTightness

/-- Truncating the source extraction list retains exactly the first requested levels. -/
theorem sourceExcursionLevels_take (m r : ℝ) (ℓ : ℕ) (b : Site) (k n d : ℕ)
    (hd : d ≤ n) :
    (sourceExcursionLevels m r ℓ b k n).take d = sourceExcursionLevels m r ℓ b k d := by
  induction d generalizing k n with
  | zero => simp [sourceExcursionLevels]
  | succ d ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [sourceExcursionLevels, List.take_succ_cons]
      rw [ih (k + 1) n (by omega)]

/-- Every intermediate population equals the actual segment count at the source extraction level. -/
theorem source_record_level_population {M : Type*} (m r : ℝ) (ℓ k j : ℕ)
    (hk : k ≤ ℓ) (hj : j ≤ ℓ - k) (b : Site) (D : Finset Site) (x : Site)
    (F : Site → PathWord → M) (ω : Sample) :
    finiteRecordLevelPopulation (ℓ - k)
      (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        F (ℓ - k) x (killedPathWord D x ω)) j =
      (actualTerminalWordRecords (sourceExcursionLevels m r ℓ b k (ℓ - k - j))
        D x ω).length := by
  rw [actual_record_level_population _ _ F _ j hj,
    source_tree_levels m r ℓ b (ℓ - k) k (by omega),
    sourceExcursionLevels_take m r ℓ b k (ℓ - k) (ℓ - k - j) (by omega)]
  rfl

end SRWTightness
