import SRWTightness.ActualRecordKernel
import SRWTightness.FiniteRecordComparison

open MeasureTheory

namespace SRWTightness

/-- The ordered finite tree extracted from a word, with the actual leaf observation F. -/
noncomputable def actualFiniteWordRecord {M : Type*} (K C : ℕ → Finset Site)
    (F : Site → PathWord → M) : (n : ℕ) → Site → PathWord → FiniteExcursionRecord M n
  | 0 => F
  | n + 1 => fun x w ↦ wordChildRecords (K n) (C n) x
      (actualFiniteWordRecord K C F n) w

/-- Joint actual finite-tree record and exit-position measure at depth n. -/
noncomputable def actualFiniteRecordSlice {M : Type*} (K C : ℕ → Finset Site)
    (F : Site → PathWord → M) (n : ℕ) (x : Site)
    (r : FiniteExcursionRecord M n) : Measure Site :=
  recordExitSlice (C n) x
    (fun ω ↦ actualFiniteWordRecord K C F n x (killedPathWord (C n) x ω)) r

instance actualFiniteRecordSlice_isFiniteMeasure {M : Type*} (K C : ℕ → Finset Site)
    (F : Site → PathWord → M) (n : ℕ) (x : Site) (r : FiniteExcursionRecord M n) :
    IsFiniteMeasure (actualFiniteRecordSlice K C F n x r) := by
  unfold actualFiniteRecordSlice
  infer_instance

/-- Total slice mass is the event probability of the actual recursively extracted tree. -/
theorem actualFiniteRecordSlice_mass {M : Type*} (K C : ℕ → Finset Site)
    (F : Site → PathWord → M) (n : ℕ) (x : Site) (r : FiniteExcursionRecord M n) :
    (actualFiniteRecordSlice K C F n x r).real Set.univ =
      pathLaw.real {ω | actualFiniteWordRecord K C F n x (killedPathWord (C n) x ω) = r} :=
  recordExitSlice_mass _ _ _ _

/-- Actual recursive trees satisfy the precise kernel recurrence, with record/exit dependence. -/
theorem actualFiniteRecordSlice_step {M : Type*} (K C : ℕ → Finset Site)
    (F : Site → PathWord → M) (n : ℕ) (hKC : K n ⊆ C n) (hCD : C n ⊆ C (n + 1))
    (x : Site) (rs : FiniteExcursionRecord M (n + 1)) :
    (actualFiniteRecordSlice K C F (n + 1) x rs).real Set.univ =
      orderedRecordWeight (competingEntranceLaw (C (n + 1)) (K n))
        (actualFiniteRecordSlice K C F n) (competingExitMass (C (n + 1)) (K n)) rs x := by
  rw [actualFiniteRecordSlice_mass]
  exact actual_ordered_record_kernel (C (n + 1)) (K n) (C n) hKC hCD
    (actualFiniteWordRecord K C F n) rs x

end SRWTightness
