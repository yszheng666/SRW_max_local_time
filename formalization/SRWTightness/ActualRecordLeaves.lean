import SRWTightness.ActualFiniteRecordKernel
import SRWTightness.NestedWordExtraction

namespace SRWTightness

/-- Ordered terminal observations of a finite record tree, with multiplicity. -/
def finiteRecordLeaves {M : Type*} : (n : ℕ) → FiniteExcursionRecord M n → List M
  | 0, r => [r]
  | n + 1, rs => rs.flatMap (finiteRecordLeaves n)

/-- The extraction domains of a tree, in the order encountered from root to leaves. -/
def actualRecordLevels (K C : ℕ → Finset Site) : ℕ → List (Finset Site × Finset Site)
  | 0 => []
  | n + 1 => (K n, C n) :: actualRecordLevels K C n

/-- Flattening the actual tree gives precisely the previous terminal word extraction. -/
theorem actualFiniteWordRecord_leaves {M : Type*} (K C : ℕ → Finset Site)
    (F : Site → PathWord → M) (n : ℕ) (x : Site) (w : PathWord) :
    finiteRecordLeaves n (actualFiniteWordRecord K C F n x w) =
      (terminalWordRecords (actualRecordLevels K C n) x w).map (fun q ↦ F q.1 q.2) := by
  induction n generalizing x w with
  | zero => simp [finiteRecordLeaves, actualFiniteWordRecord, actualRecordLevels, terminalWordRecords]
  | succ n ih =>
    simp only [finiteRecordLeaves, actualFiniteWordRecord, wordChildRecords, actualRecordLevels,
      terminalWordRecords, List.flatMap_map, List.map_flatMap, ih]

end SRWTightness
