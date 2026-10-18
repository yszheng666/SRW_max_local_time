import SRWTightness.RootOuterDomainGeometry

namespace SRWTightness

/-- A one-step distance gap keeps every exit from the first disk outside the second disk. -/
theorem translated_disk_exit_gap (b w : Site) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hgap : r + s + 1 ≤ Real.sqrt (normSq (w - b))) :
    ∀ y ∈ domainExitBoundary (translateFinset b (diskFinset r)),
      y ∉ translateFinset w (diskFinset s) := by
  intro y hy hother
  have hrad := (translated_disk_boundary_radial b r hr y hy).2
  have hnon := Real.sqrt_nonneg (normSq (y - b))
  have hsquare := normSq_eq_sq_sqrt (y - b)
  have hybound : normSq (y - b) ≤ (r + 1) ^ 2 := by nlinarith
  have hwbound : normSq (w - y) < s ^ 2 := by
    have hp : normSq (y - w) < s ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hother
    simpa only [show w - y = -(y - w) by abel, normSq_neg] using hp
  have hsum := normSq_add_lt_of_le_of_lt (y - b) (w - y) (by linarith : 0 ≤ r + 1)
    hs hybound hwbound
  rw [show (y - b) + (w - y) = w - b by abel] at hsum
  have hdist := normSq_eq_sq_sqrt (w - b)
  have hnonDist := Real.sqrt_nonneg (normSq (w - b))
  nlinarith

end SRWTightness
