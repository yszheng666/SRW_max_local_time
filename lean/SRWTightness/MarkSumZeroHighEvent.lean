import SRWTightness.ProjectedMarkChernoff

open MeasureTheory

namespace SRWTightness

/-- Zero marks cannot put every site in a nonempty observation set above a positive threshold. -/
theorem markSum_zero_all_high_probability (D A : Finset Site) (hA : A.Nonempty)
    (α level : ℝ) (hlevel : 0 < level) :
    (markProductLaw D A α 0).real
      {Y | ∀ v : A, level ≤ (sumMarks A 0 Y v : ℝ)} = 0 := by
  have he : {Y : MarkSamples A 0 | ∀ v : A, level ≤ (sumMarks A 0 Y v : ℝ)} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr (fun Y hY ↦ ?_)
    obtain ⟨z, hz⟩ := hA
    have h : level ≤ 0 := by simpa [sumMarks] using hY ⟨z, hz⟩
    linarith
  rw [he]
  simp

end SRWTightness
