import SRWTightness.SourceRecordTreePopulation

namespace SRWTightness

/-- Each tree population counts the actual word segments extracted down to that level. -/
theorem actual_record_level_population {M : Type*} (K C : ℕ → Finset Site)
    (F : Site → PathWord → M) (n j : ℕ) (hj : j ≤ n) (x : Site) (w : PathWord) :
    finiteRecordLevelPopulation n (actualFiniteWordRecord K C F n x w) j =
      (terminalWordRecords ((actualRecordLevels K C n).take (n - j)) x w).length := by
  induction n generalizing j x w with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    simp [actualFiniteWordRecord, finiteRecordLevelPopulation, actualRecordLevels,
      terminalWordRecords]
  | succ n ih =>
    by_cases htop : j = n + 1
    · subst j
      simp [finiteRecordLevelPopulation, terminalWordRecords]
    · have hjn : j ≤ n := by omega
      have hsub : n + 1 - j = (n - j) + 1 := by omega
      simp only [actualFiniteWordRecord, finiteRecordLevelPopulation, if_neg htop,
        actualRecordLevels, hsub, List.take_succ_cons, terminalWordRecords,
        wordChildRecords, List.map_map, Function.comp_def, List.length_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro q hq
      exact ih j hjn _ _

end SRWTightness
