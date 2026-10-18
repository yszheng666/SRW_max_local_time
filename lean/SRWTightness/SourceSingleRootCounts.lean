import SRWTightness.SourceForwardRecordCounts

namespace SRWTightness

/-- Counts inside one prescribed level-k root, including the root itself exactly once. -/
noncomputable def sourceSingleRootCount (m r : ℝ) (ℓ k i : ℕ) (b : Site)
    (x : Site) (ω : Sample) : ℕ :=
  if i = k then 1 else sourceForwardRecordCount m r ℓ (k + 1) i b
    (sourceExitDomain m r ℓ b k) x ω

/-- Every forward generation inside a single root has the correctly shifted tree population. -/
theorem source_single_root_population {M : Type*} (m r : ℝ) (ℓ k i : ℕ)
    (hki : k ≤ i) (hi : i < ℓ) (b : Site) (x : Site)
    (F : Site → PathWord → M) (ω : Sample) :
    finiteRecordLevelPopulation (ℓ - (k + 1))
      (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        F (ℓ - (k + 1)) x (killedPathWord (sourceExitDomain m r ℓ b k) x ω))
      (ℓ - (i + 1)) = sourceSingleRootCount m r ℓ k i b x ω := by
  by_cases hik : i = k
  · subst i
    simp only [sourceSingleRootCount, ite_true, finiteRecordLevelPopulation_root]
  · rw [sourceSingleRootCount, if_neg hik]
    exact source_forward_record_population m r ℓ (k + 1) i (by omega) hi b
      (sourceExitDomain m r ℓ b k) x F ω

end SRWTightness
