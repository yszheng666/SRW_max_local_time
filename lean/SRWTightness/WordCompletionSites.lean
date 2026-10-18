import SRWTightness.WordMark

namespace SRWTightness

/-- The actual completion locations of one label, with repetitions retained. -/
def wordMarkCompletionSites (L C : Finset Site) : WordMark → List Site
  | none => []
  | some (x, w) => (wordChildIntervals L C x w).map
      (fun q ↦ x + position (wordPath w) q.2)

/-- Completion-site sums may be grouped by label; this list is not a chronological merge. -/
def wordMarkPairCompletionSites (L₁ C₁ L₂ C₂ : Finset Site) (Y : WordMark) : List Site :=
  wordMarkCompletionSites L₁ C₁ Y ++ wordMarkCompletionSites L₂ C₂ Y

theorem wordMarkCompletionSites_length (L C : Finset Site) (Y : WordMark) :
    (wordMarkCompletionSites L C Y).length = wordMarkRootCount L C Y := by
  cases Y with
  | none => rfl
  | some p => rcases p with ⟨x, w⟩; simp [wordMarkCompletionSites, wordMarkRootCount]

theorem wordMarkPairCompletionSites_length (L₁ C₁ L₂ C₂ : Finset Site) (Y : WordMark) :
    (wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y).length =
      wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y := by
  simp [wordMarkPairCompletionSites, wordMarkCompletionSites_length]

/-- Repeated completion positions contribute once per completed root. -/
theorem completion_site_sum_le (xs : List Site) (f : Site → ℝ) (B : ℝ)
    (hf : ∀ x ∈ xs, f x ≤ B) : (xs.map f).sum ≤ (xs.length : ℝ) * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy ↦ hf y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- The completion sum is controlled by the actual total root count, not distinct sites. -/
theorem wordMarkPairCompletionSites_sum_le (L₁ C₁ L₂ C₂ : Finset Site)
    (Y : WordMark) (f : Site → ℝ) (B : ℝ)
    (hf : ∀ x ∈ wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y, f x ≤ B) :
    ((wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y).map f).sum ≤
      ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ) * B := by
  simpa only [wordMarkPairCompletionSites_length] using
    completion_site_sum_le (wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y) f B hf

end SRWTightness
