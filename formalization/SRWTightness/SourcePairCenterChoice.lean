import SRWTightness.SourcePairShellSites

namespace SRWTightness

/-- The center-coordinate family in the late-pair sum exists for every positive base radius. -/
theorem source_pair_center_choice (A : ℝ) (I : ℕ) (hA : 0 < A) :
    ∃ z : ∀ b : Site, translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
      ∀ b : Site, (z b : Site) = b := by
  have hr : 0 < A * diskEnergyGapRatio ^ I :=
    mul_pos hA (pow_pos (by linarith [diskEnergyGapRatio_gt_four]) _)
  have hm (b : Site) : b ∈ translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)) := by
    rw [mem_translateFinset_iff, sub_self]
    exact zero_mem_diskFinset _ hr
  exact ⟨fun b ↦ ⟨b, hm b⟩, fun _ ↦ rfl⟩

end SRWTightness
