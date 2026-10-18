import SRWTightness.RecordRadialSupport

open MeasureTheory

namespace SRWTightness

/-- The inner entrance layer is unchanged when the outer killing domain has any shape or center. -/
theorem competingEntranceLaw_radial_support_domain (D : Finset Site) (b : Site) (a : ℝ) (ha : 1 ≤ a) (x : Site)
    (hx : x ∈ D \ translateFinset b (diskFinset a)) :
    ∀ᵐ y ∂competingEntranceLaw (D)
      (translateFinset b (diskFinset a)) x,
      a - 1 ≤ Real.sqrt (normSq (y - b)) ∧ Real.sqrt (normSq (y - b)) ≤ a := by
  filter_upwards [competingEntranceLaw_supported_boundary _ _ x hx] with y hy
  obtain ⟨_, z, hz, d, he⟩ := hy.1
  have hzl : a ^ 2 ≤ normSq (z - b) := by
    have hn := (Finset.mem_sdiff.mp hz).2
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq, not_lt] using hn
  have hyl : (a - 1) ^ 2 ≤ normSq (y - b) := by
    rw [he, show z + step d - b = (z - b) + step d by abel]
    exact normSq_step_lower (z - b) d a ha hzl
  have hyu : normSq (y - b) ≤ a ^ 2 := by
    have hh : normSq (y - b) < a ^ 2 := by
      simpa only [Finset.mem_coe, mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hy.2
    exact hh.le
  exact ⟨(Real.le_sqrt (by linarith) (normSq_nonneg _)).mpr hyl,
    (Real.sqrt_le_left (by linarith)).mpr hyu⟩

end SRWTightness
