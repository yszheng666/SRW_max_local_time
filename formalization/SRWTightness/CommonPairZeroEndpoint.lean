import SRWTightness.MarkSumZeroHighEvent
import SRWTightness.CommonPairPositiveEndpoints

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- A positive threshold at any retained site is impossible with zero marks. -/
theorem projected_mark_zero_high_probability (D K A : Finset Site)
    (hAK : A ⊆ K) (hA : A.Nonempty) (α level : ℝ) (hlevel : 0 < level) :
    (markProductLaw D K α 0).real
      {Y | ∀ v : A, level ≤ (sumMarks K 0 Y ⟨v, hAK v.property⟩ : ℝ)} = 0 := by
  have he : {Y : MarkSamples K 0 |
      ∀ v : A, level ≤ (sumMarks K 0 Y ⟨v, hAK v.property⟩ : ℝ)} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr (fun Y hY ↦ ?_)
    obtain ⟨z, hz⟩ := hA
    have h : level ≤ 0 := by simpa [sumMarks] using hY ⟨z, hz⟩
    linarith
  rw [he]
  simp

/-- Adding the zero population endpoint leaves a sum with vanishing zero term unchanged. -/
theorem common_pair_sum_include_zero (q : ℝ) (f : ℕ → ℝ) (hzero : f 0 = 0) :
    (∑ k ∈ Finset.range (⌊q ^ 2 / 2⌋₊ + 1), f k) =
      ∑ k ∈ commonPairPositiveEndpoints q, f k := by
  rw [commonPairPositiveEndpoints, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : 0 < k
  · simp [h]
  · have hk0 : k = 0 := by omega
    simp [hk0, hzero]

end SRWTightness
