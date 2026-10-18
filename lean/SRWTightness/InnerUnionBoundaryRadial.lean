import SRWTightness.GeneralEntranceRadialSupport

namespace SRWTightness

/-- Entering a union target through one component disk places the entrance in that disk's inner unit layer. -/
theorem inner_union_boundary_radial (D K : Finset Site) (b : Site) (a : ℝ) (ha : 1 ≤ a)
    (hK : translateFinset b (diskFinset a) ⊆ K) (y : Site)
    (hy : y ∈ domainExitBoundary (D \ K)) (hyK : y ∈ translateFinset b (diskFinset a)) :
    a - 1 ≤ Real.sqrt (normSq (y - b)) ∧ Real.sqrt (normSq (y - b)) ≤ a := by
  obtain ⟨_, z, hz, d, he⟩ := hy
  have hzl : a ^ 2 ≤ normSq (z - b) := by
    have hn : z ∉ translateFinset b (diskFinset a) := fun h ↦ (Finset.mem_sdiff.mp hz).2 (hK h)
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq, not_lt] using hn
  have hyl : (a - 1) ^ 2 ≤ normSq (y - b) := by
    rw [he, show z + step d - b = (z - b) + step d by abel]
    exact normSq_step_lower (z - b) d a ha hzl
  have hyu : normSq (y - b) ≤ a ^ 2 := by
    have hh : normSq (y - b) < a ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hyK
    exact hh.le
  exact ⟨(Real.le_sqrt (by linarith) (normSq_nonneg _)).mpr hyl,
    (Real.sqrt_le_left (by linarith)).mpr hyu⟩

end SRWTightness
