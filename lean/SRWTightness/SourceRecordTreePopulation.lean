import SRWTightness.SourceRecordTreeLeaves
import SRWTightness.FiniteRecordErrorCount

open scoped BigOperators

namespace SRWTightness

/-- Terminal population counts exactly the leaves, including extinction. -/
theorem finiteRecordLeaves_length {M : Type*} (n : ℕ) (r : FiniteExcursionRecord M n) :
    (finiteRecordLeaves n r).length = finiteRecordLevelPopulation n r 0 := by
  induction n with
  | zero => simp [finiteRecordLeaves, finiteRecordLevelPopulation]
  | succ n ih =>
    simp [finiteRecordLeaves, List.length_flatMap, finiteRecordLevelPopulation, ih]

/-- The terminal population of the actual source tree is the actual terminal segment count. -/
theorem source_record_tree_terminal_population {M : Type*} (m r : ℝ) (ℓ k : ℕ)
    (hk : k ≤ ℓ) (b : Site) (D : Finset Site) (x : Site)
    (F : Site → PathWord → M) (ω : Sample) :
    finiteRecordLevelPopulation (ℓ - k)
      (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        F (ℓ - k) x (killedPathWord D x ω)) 0 =
      (sourceTerminalRecords m r ℓ k b D x ω).length := by
  rw [← finiteRecordLeaves_length, source_record_tree_leaves m r ℓ k hk, List.length_map]

/-- A uniform terminal error is charged once per actual terminal individual. -/
theorem finiteRecordTerminalError_constant {M : Type*} (ε : ℝ) (n : ℕ)
    (r : FiniteExcursionRecord M n) :
    finiteRecordTerminalError (fun _ ↦ ε) n r = ε * (finiteRecordLevelPopulation n r 0 : ℝ) := by
  induction n with
  | zero => simp [finiteRecordTerminalError, finiteRecordLevelPopulation]
  | succ n ih =>
    simp only [finiteRecordTerminalError, finiteRecordLevelPopulation,
      if_neg (show 0 ≠ n + 1 by omega)]
    induction r with
    | nil => simp
    | cons v vs ihs =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.cast_add, mul_add] at ⊢ ihs
      rw [ihs]

/-- The actual source tree error has the adjacent-population sum and actual terminal count. -/
theorem source_record_tree_error {M : Type*} (m r : ℝ) (ℓ k : ℕ) (hk : k ≤ ℓ)
    (b : Site) (D : Finset Site) (x : Site) (F : Site → PathWord → M)
    (ω : Sample) (δ : ℕ → ℝ) (ε : ℝ) :
    let tree := actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
      F (ℓ - k) x (killedPathWord D x ω)
    finiteRecordError δ (fun _ ↦ ε) (ℓ - k) tree =
      (∑ j ∈ Finset.range (ℓ - k),
        ((finiteRecordLevelPopulation (ℓ - k) tree (j + 1) : ℝ) +
          (finiteRecordLevelPopulation (ℓ - k) tree j : ℝ)) * δ j) +
        ε * (sourceTerminalRecords m r ℓ k b D x ω).length := by
  dsimp only
  rw [finiteRecordError_population_sum, finiteRecordTerminalError_constant,
    source_record_tree_terminal_population m r ℓ k hk]

end SRWTightness
