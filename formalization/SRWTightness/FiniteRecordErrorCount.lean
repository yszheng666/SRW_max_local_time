import SRWTightness.FiniteRecordComparison

open scoped BigOperators

namespace SRWTightness

/-- Number of entrance/exit decisions at a fixed level counted up from the terminal generation. -/
def finiteRecordLevelDecisions {M : Type*} : (n : ℕ) → FiniteExcursionRecord M n → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, rs, j => if j = n then rs.length + 1
      else (rs.map (fun r ↦ finiteRecordLevelDecisions n r j)).sum

/-- Sum of errors on all terminal marks, with no contribution from extinct branches. -/
def finiteRecordTerminalError {M : Type*} (η : M → ℝ) :
    (n : ℕ) → FiniteExcursionRecord M n → ℝ
  | 0, m => η m
  | n + 1, rs => (rs.map (finiteRecordTerminalError η n)).sum

/-- The recursive record error is exactly a sum over level decision counts and terminal marks. -/
theorem finiteRecordError_level_sum {M : Type*} (δ : ℕ → ℝ) (η : M → ℝ) :
    ∀ n (r : FiniteExcursionRecord M n),
      finiteRecordError δ η n r =
        (∑ j ∈ Finset.range n, (finiteRecordLevelDecisions n r j : ℝ) * δ j) +
          finiteRecordTerminalError η n r := by
  intro n
  induction n with
  | zero => intro r; simp [finiteRecordError, finiteRecordTerminalError]
  | succ n ih =>
    intro rs
    have hs : (rs.map (finiteRecordError δ η n)).sum =
        (∑ j ∈ Finset.range n,
          ((rs.map (fun r ↦ finiteRecordLevelDecisions n r j)).sum : ℕ) * δ j) +
            (rs.map (finiteRecordTerminalError η n)).sum := by
      induction rs with
      | nil => simp
      | cons r rs ihs =>
        simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_mul,
          Finset.sum_add_distrib, ih r, ihs]
        ring
    rw [finiteRecordError, orderedRecordError_sum, hs, Finset.sum_range_succ]
    have hc : (∑ j ∈ Finset.range n,
        (finiteRecordLevelDecisions (n + 1) rs j : ℝ) * δ j) =
        ∑ j ∈ Finset.range n,
          ((rs.map (fun r ↦ finiteRecordLevelDecisions n r j)).sum : ℕ) * δ j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [finiteRecordLevelDecisions, if_neg (ne_of_lt (Finset.mem_range.mp hj))]
    rw [hc]
    simp only [finiteRecordLevelDecisions, if_pos rfl, ite_true, finiteRecordTerminalError,
      Nat.cast_add, Nat.cast_one]
    ring

/-- Population at a fixed remaining depth; the root has remaining depth n. -/
def finiteRecordLevelPopulation {M : Type*} : (n : ℕ) → FiniteExcursionRecord M n → ℕ → ℕ
  | 0, _, j => if j = 0 then 1 else 0
  | n + 1, rs, j => if j = n + 1 then 1
      else (rs.map (fun r ↦ finiteRecordLevelPopulation n r j)).sum

theorem finiteRecordLevelPopulation_root {M : Type*} (n : ℕ)
    (r : FiniteExcursionRecord M n) : finiteRecordLevelPopulation n r n = 1 := by
  cases n <;> simp [finiteRecordLevelPopulation]

/-- Summing child counts plus one over parents gives the two adjacent generation populations. -/
theorem finiteRecordLevelDecisions_eq_populations {M : Type*} :
    ∀ n (r : FiniteExcursionRecord M n) j, j < n →
      finiteRecordLevelDecisions n r j =
        finiteRecordLevelPopulation n r (j + 1) + finiteRecordLevelPopulation n r j := by
  intro n
  induction n with
  | zero => intro r j hj; omega
  | succ n ih =>
    intro rs j hj
    by_cases he : j = n
    · subst j
      have hs : (rs.map (fun r ↦ finiteRecordLevelPopulation n r n)).sum = rs.length := by
        induction rs with
        | nil => simp
        | cons r rs ihs => simp [finiteRecordLevelPopulation_root, ihs, Nat.add_comm]
      simp only [finiteRecordLevelDecisions, if_pos rfl, ite_true, finiteRecordLevelPopulation,
        if_neg (show n ≠ n + 1 by omega)]
      rw [hs]
      omega
    · have hjn : j < n := by omega
      have hs : (rs.map (fun r ↦ finiteRecordLevelDecisions n r j)).sum =
          (rs.map (fun r ↦ finiteRecordLevelPopulation n r (j + 1))).sum +
            (rs.map (fun r ↦ finiteRecordLevelPopulation n r j)).sum := by
        induction rs with
        | nil => simp
        | cons r rs ihs =>
          simp only [List.map_cons, List.sum_cons, ih r j hjn, ihs]
          omega
      simpa only [finiteRecordLevelDecisions, if_neg he, finiteRecordLevelPopulation,
        if_neg (show j + 1 ≠ n + 1 by omega), if_neg (show j ≠ n + 1 by omega)] using hs

/-- The exact adjacent-population error sum appearing in the record comparison. -/
theorem finiteRecordError_population_sum {M : Type*} (δ : ℕ → ℝ) (η : M → ℝ)
    (n : ℕ) (r : FiniteExcursionRecord M n) :
    finiteRecordError δ η n r =
      (∑ j ∈ Finset.range n,
        ((finiteRecordLevelPopulation n r (j + 1) : ℝ) +
          (finiteRecordLevelPopulation n r j : ℝ)) * δ j) + finiteRecordTerminalError η n r := by
  rw [finiteRecordError_level_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [finiteRecordLevelDecisions_eq_populations n r j (Finset.mem_range.mp hj), Nat.cast_add]

end SRWTightness
