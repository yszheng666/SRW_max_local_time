import SRWTightness.MarkSumGenerating
import SRWTightness.LatticeTranslation

open MeasureTheory
namespace SRWTightness

/-- Elementary spatial translation invariance of projected reference-mark occupation events.
This is an explicit external foundation, not a proved theorem or a tail estimate. -/
def ProjectedMarkTranslationInput : Prop :=
  ∀ (b : Site) (D A K : Finset Site) (hAK : A ⊆ K) (α : ℝ) (k a : ℕ),
    (markProductLaw (translateFinset b D) (translateFinset b K) α k).real
      {Y | ∃ z : A, a ≤ sumMarks (translateFinset b K) k Y
        ⟨b + z, (mem_translateFinset_add b K z).2 (hAK z.property)⟩} =
    (markProductLaw D K α k).real
      {Y | ∃ z : A, a ≤ sumMarks K k Y ⟨z, hAK z.property⟩}

end SRWTightness
