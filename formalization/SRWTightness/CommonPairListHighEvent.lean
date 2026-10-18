import SRWTightness.MarkSumGenerating
import SRWTightness.TerminalListSamples

open MeasureTheory
namespace SRWTightness

/-- The retained sites' high-occupation event decoded from an ordered list of terminal marks. -/
def commonPairListHighEvent (K A : Finset Site) (hAK : A ⊆ K) (k : ℕ) (level : ℝ) :
    Set (List (Mark K)) :=
  {rs | ∀ v : A, level ≤ (sumMarks K k (terminalListSamples 0 k rs) ⟨v, hAK v.property⟩ : ℝ)}

/-- Decoding the independent leaf list recovers exactly the finite mark-product high event. -/
theorem common_pair_list_high_probability (D K A : Finset Site) (hAK : A ⊆ K)
    (α level : ℝ) (k : ℕ)
    [MeasurableSpace (List (Mark K))] [MeasurableSingletonClass (List (Mark K))] :
    independentForestLaw (referenceMarkLaw D K α) k (commonPairListHighEvent K A hAK k level) =
      markProductLaw D K α k {Y | ∀ v : A, level ≤ (sumMarks K k Y ⟨v, hAK v.property⟩ : ℝ)} := by
  have hh := congrArg (fun μ : Measure (MarkSamples K k) ↦
    μ {Y | ∀ v : A, level ≤ (sumMarks K k Y ⟨v, hAK v.property⟩ : ℝ)})
    (terminalListSamples_law (referenceMarkLaw D K α) (0 : Mark K) k)
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _ |>.measurableSet)] at hh
  exact hh

end SRWTightness
