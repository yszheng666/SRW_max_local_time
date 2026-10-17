import SRWTightness.FirstEntranceRootPreservation

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- The original killed word and the first-entry mark have the same joint two-label root law. -/
theorem firstEntranceWordMark_pair_root_law (D K L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ K) (hL₂ : L₂ ⊆ K) (x : Site) :
    (killedWordMarkLaw D x).map (fun Y ↦
      (wordMarkRootCount L₁ C₁ Y, wordMarkRootCount L₂ C₂ Y)) =
    (firstEntranceWordMarkLaw D K x).map (fun Y ↦
      (wordMarkRootCount L₁ C₁ Y, wordMarkRootCount L₂ C₂ Y)) := by
  rw [killedWordMarkLaw, firstEntranceWordMarkLaw,
    Measure.map_map (measurable_of_countable _) (measurable_killedWordMark D x),
    Measure.map_map (measurable_of_countable _) (measurable_firstEntranceWordMark D K x)]
  exact Measure.map_congr (firstEntranceWordMark_pair_root_count_ae D K L₁ C₁ L₂ C₂ hL₁ hL₂ x)

/-- All nonnegative joint root tests transfer, including unbounded exponential moments. -/
theorem firstEntranceWordMark_pair_root_lintegral (D K L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ K) (hL₂ : L₂ ⊆ K) (x : Site) (F : ℕ × ℕ → ℝ≥0∞) :
    (∫⁻ ω, F (wordMarkRootCount L₁ C₁ (killedWordMark D x ω),
      wordMarkRootCount L₂ C₂ (killedWordMark D x ω)) ∂pathLaw) =
    ∫⁻ Y, F (wordMarkRootCount L₁ C₁ Y, wordMarkRootCount L₂ C₂ Y)
      ∂firstEntranceWordMarkLaw D K x := by
  rw [firstEntranceWordMarkLaw,
    lintegral_map (measurable_of_countable _) (measurable_firstEntranceWordMark D K x)]
  apply lintegral_congr_ae
  filter_upwards [firstEntranceWordMark_pair_root_count_ae D K L₁ C₁ L₂ C₂ hL₁ hL₂ x]
    with ω hω
  exact congrArg F hω

end SRWTightness
