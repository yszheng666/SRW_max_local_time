import SRWTightness.RootBinomialMoment
import SRWTightness.ChildIntervalInterior
import SRWTightness.ChildIntervalOrder

open MeasureTheory

namespace SRWTightness

/-- Each complete word child exits by one nearest-neighbor step from its own domain. -/
theorem word_child_completion_boundary (L C : Finset Site) (hLC : L ⊆ C)
    (x : Site) (w : PathWord) (q : ℕ × ℕ) (hq : q ∈ wordChildIntervals L C x w) :
    x + position (wordPath w) q.2 ∈ domainExitBoundary C := by
  have hlt : q.1 < q.2 := scanChildIntervals_start_lt_end L C x (wordPath w) _
    List.pairwise_lt_range none (by intro a h; cases h) q hq
  have hin : x + position (wordPath w) (q.2 - 1) ∈ C :=
    wordChildIntervals_interior L C hLC x w q hq _ (by omega) (by omega)
  have hout := (wordChildIntervals_endpoints L C x w q hq).2
  refine ⟨hout, x + position (wordPath w) (q.2 - 1), hin, (wordPath w) (q.2 - 1), ?_⟩
  have he : q.2 = (q.2 - 1) + 1 := by omega
  have hp : position (wordPath w) q.2 = position (wordPath w) (q.2 - 1) +
      step ((wordPath w) (q.2 - 1)) := by
    calc
      _ = position (wordPath w) ((q.2 - 1) + 1) := congrArg (position (wordPath w)) he
      _ = _ := rfl
  rw [hp, add_assoc]

/-- Every retained completion of one label belongs to its actual exterior boundary. -/
theorem word_mark_completion_boundary (L C : Finset Site) (hLC : L ⊆ C)
    (Y : WordMark) (z : Site) (hz : z ∈ wordMarkCompletionSites L C Y) :
    z ∈ domainExitBoundary C := by
  cases Y with
  | none => simp [wordMarkCompletionSites] at hz
  | some p =>
    rcases p with ⟨x, w⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact word_child_completion_boundary L C hLC x w q hq

/-- Pair completion lists preserve the exact union of the two actual exterior boundaries. -/
theorem word_mark_pair_completion_boundary (L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂) (Y : WordMark) (z : Site)
    (hz : z ∈ wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y) :
    z ∈ rootCompletionSet C₁ C₂ := by
  change z ∈ wordMarkCompletionSites L₁ C₁ Y ++ wordMarkCompletionSites L₂ C₂ Y at hz
  change z ∈ domainExitBoundary C₁ ∨ z ∈ domainExitBoundary C₂
  rcases List.mem_append.mp hz with hz | hz
  · exact Or.inl (word_mark_completion_boundary L₁ C₁ hL₁ Y z hz)
  · exact Or.inr (word_mark_completion_boundary L₂ C₂ hL₂ Y z hz)

/-- The actual killed-word pair completion law has the full original boundary support. -/
theorem finite_root_completion_support_internal (D L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂) (x : Site) :
    ∀ᵐ Y ∂killedWordMarkLaw D x,
      ∀ z ∈ wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y, z ∈ rootCompletionSet C₁ C₂ :=
  Filter.Eventually.of_forall (fun Y z hz ↦
    word_mark_pair_completion_boundary L₁ C₁ L₂ C₂ hL₁ hL₂ Y z hz)

end SRWTightness
