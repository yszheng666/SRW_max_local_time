import SRWTightness.MarkSumZeroHighEvent

open MeasureTheory
namespace SRWTightness

/-- With no marks, a positive visit cutoff cannot be reached anywhere in a projected block. -/
theorem markSum_zero_projected_max_probability (D K A : Finset Site) (hAK : A ⊆ K)
    (α : ℝ) (a : ℕ) (ha : 1 ≤ a) :
    (markProductLaw D K α 0).real
      {Y | ∃ z : A, a ≤ sumMarks K 0 Y ⟨z, hAK z.property⟩} = 0 := by
  have he : {Y : MarkSamples K 0 |
      ∃ z : A, a ≤ sumMarks K 0 Y ⟨z, hAK z.property⟩} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr (fun Y hY ↦ ?_)
    obtain ⟨z, hz⟩ := hY
    have h : a ≤ 0 := by simpa [sumMarks] using hz
    omega
  rw [he]
  simp

end SRWTightness
