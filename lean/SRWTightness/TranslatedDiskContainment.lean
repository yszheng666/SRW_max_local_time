import SRWTightness.TranslatedDiskGeometry
import SRWTightness.DiskCapacityLogBound

namespace SRWTightness

/-- A bound on the displacement of centers gives containment of translated lattice disks. -/
theorem translated_disk_subset_of_displacement (x z : Site) (a r R : ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hshift : normSq (x - z) ≤ a ^ 2)
    (hfit : a + r ≤ R) :
    translateFinset x (diskFinset r) ⊆ translateFinset z (diskFinset R) := by
  intro y hy
  have hy' : normSq (y - x) < r ^ 2 := by
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hy
  have hh := normSq_add_lt_of_le_of_lt (x - z) (y - x) ha hr hshift hy'
  rw [show x - z + (y - x) = y - z by abel] at hh
  have hin : y - z ∈ diskFinset (a + r) := (mem_diskFinset _ _).mpr hh
  exact (mem_translateFinset_iff z _ y).mpr (diskFinset_mono _ _ (by positivity) hfit hin)

end SRWTightness
