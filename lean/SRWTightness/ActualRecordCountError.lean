import SRWTightness.ActualRecordLevelPopulation

open scoped BigOperators

namespace SRWTightness

/-- Every error term is charged to actual extracted segments, at every intermediate level. -/
theorem actual_record_count_error {M : Type*} (K C : ℕ → Finset Site)
    (F : Site → PathWord → M) (n : ℕ) (x : Site) (w : PathWord)
    (δ : ℕ → ℝ) (ε : ℝ) :
    let N := fun j ↦ (terminalWordRecords ((actualRecordLevels K C n).take (n - j)) x w).length
    finiteRecordError δ (fun _ ↦ ε) n (actualFiniteWordRecord K C F n x w) =
      (∑ j ∈ Finset.range n, ((N (j + 1) : ℝ) + (N j : ℝ)) * δ j) + ε * (N 0 : ℝ) := by
  dsimp only
  rw [finiteRecordError_population_sum, finiteRecordTerminalError_constant,
    actual_record_level_population K C F n 0 (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  rw [actual_record_level_population K C F n (j + 1) (by omega),
    actual_record_level_population K C F n j (by omega)]

end SRWTightness
