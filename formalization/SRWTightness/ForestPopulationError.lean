import SRWTightness.SourceRecordTreePopulation
import SRWTightness.SourceActualRootList

open scoped BigOperators

namespace SRWTightness

/-- Total generation population across all roots, indexed by remaining depth. -/
def forestLevelPopulation {M : Type*} (n : ℕ)
    (rs : List (FiniteExcursionRecord M n)) (i : ℕ) : ℕ :=
  (rs.map (fun r ↦ finiteRecordLevelPopulation n r i)).sum

/-- Forest comparison errors sum to adjacent generation counts and the terminal count. -/
theorem forest_error_population_sum {M : Type*} (δ : ℕ → ℝ) (ε : ℝ) (n : ℕ)
    (rs : List (FiniteExcursionRecord M n)) :
    (rs.map (finiteRecordError δ (fun _ ↦ ε) n)).sum =
      (∑ i ∈ Finset.range n,
        ((forestLevelPopulation n rs (i + 1) : ℝ) + forestLevelPopulation n rs i) * δ i) +
        ε * forestLevelPopulation n rs 0 := by
  induction rs with
  | nil => simp [forestLevelPopulation]
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, finiteRecordError_population_sum,
      finiteRecordTerminalError_constant] at ⊢ ih
    rw [ih]
    simp only [forestLevelPopulation, List.map_cons, List.sum_cons, Nat.cast_add]
    simp only [add_add_add_comm, add_mul, Finset.sum_add_distrib, mul_add]

/-- Deterministic generation bounds give the event-wide error required by the forest comparison. -/
theorem forest_error_population_bound {M : Type*} (δ : ℕ → ℝ) (ε : ℝ) (n : ℕ)
    (rs : List (FiniteExcursionRecord M n)) (L : ℕ → ℝ)
    (hδ : ∀ i < n, 0 ≤ δ i) (hε : 0 ≤ ε)
    (hL : ∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ L i) :
    (rs.map (finiteRecordError δ (fun _ ↦ ε) n)).sum ≤
      (∑ i ∈ Finset.range n, (L (i + 1) + L i) * δ i) + ε * L 0 := by
  rw [forest_error_population_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i hi
    have hin := Finset.mem_range.mp hi
    exact mul_le_mul_of_nonneg_right
      (add_le_add (hL (i + 1) (by omega)) (hL i (by omega))) (hδ i hin)
  · exact mul_le_mul_of_nonneg_left (hL 0 (Nat.zero_le _)) hε

/-- The forest generation populations equal the actual forward manuscript segment counts. -/
theorem source_forest_population {M : Type*} (m r : ℝ) (ℓ k i : ℕ)
    (hki : k ≤ i) (hi : i < ℓ) (b : Site) (D : Finset Site) (x : Site)
    (F : Site → PathWord → M) (ω : Sample) :
    forestLevelPopulation (ℓ - (k + 1))
      (killedChildRecords D (sourceEntranceDomain m r ℓ b k)
        (sourceExitDomain m r ℓ b k) x
        (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
          F (ℓ - (k + 1))) ω) (ℓ - (i + 1)) =
      sourceForwardRecordCount m r ℓ k i b D x ω := by
  have hk : k < ℓ := by omega
  have hh := source_forward_record_population m r ℓ k i hki hi b D x F ω
  have hdepth : ℓ - k = ℓ - (k + 1) + 1 := by omega
  rw [hdepth, source_actual_root_list m r ℓ k hk] at hh
  simpa only [finiteRecordLevelPopulation, if_neg (show ℓ - (i + 1) ≠
    ℓ - (k + 1) + 1 by omega), forestLevelPopulation, killedChildRecords] using hh

end SRWTightness
