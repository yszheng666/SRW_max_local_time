import SRWTightness.WordCompletionSites
import Mathlib.Data.Nat.Choose.Sum

namespace SRWTightness

/-- Grouping selections by their last index gives the finite root-selection identity. -/
theorem root_selection_count (n p : ℕ) :
    ∑ i ∈ Finset.range n, i.choose p = n.choose (p + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
    simp only [Nat.succ_eq_add_one]
    omega

/-- The combinatorial identity uses the actual total count of both labels on one mark. -/
theorem wordMarkPair_root_selection_count (L₁ C₁ L₂ C₂ : Finset Site)
    (Y : WordMark) (p : ℕ) :
    ∑ i ∈ Finset.range (wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y).length, i.choose p =
      (wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y).choose (p + 1) := by
  rw [root_selection_count, wordMarkPairCompletionSites_length]

/-- Grouping by the first selected root leaves n-1-i possible later roots. -/
theorem root_first_selection_count (n p : ℕ) :
    ∑ i ∈ Finset.range n, (n - 1 - i).choose p = n.choose (p + 1) := by
  exact (Finset.sum_range_reflect (fun i : ℕ ↦ i.choose p) n).trans
    (root_selection_count n p)

/-- The first-selection count applies to the actual two-label completion multiplicity. -/
theorem wordMarkPair_first_selection_count (L₁ C₁ L₂ C₂ : Finset Site)
    (Y : WordMark) (p : ℕ) :
    let n := (wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y).length
    ∑ i ∈ Finset.range n, (n - 1 - i).choose p =
      (wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y).choose (p + 1) := by
  dsimp only
  rw [root_first_selection_count, wordMarkPairCompletionSites_length]

end SRWTightness
