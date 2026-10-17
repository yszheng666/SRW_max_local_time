import SRWTightness.GreenTranslation
import SRWTightness.GeometryTriangle
import SRWTightness.LatticeNorm
import SRWTightness.DiskOnePoint

namespace SRWTightness

theorem normSq_add_lt_of_le_of_lt (x y : Site) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : normSq x ≤ a ^ 2) (hy : normSq y < b ^ 2) : normSq (x + y) < (a + b) ^ 2 := by
  have hsy : Real.sqrt (normSq y) < b := (Real.sqrt_lt (normSq_nonneg y) hb).mpr hy
  have hh := normSq_add_bound x y ha (Real.sqrt_nonneg _) hx
    (le_of_eq (normSq_eq_sq_sqrt y))
  have hnon := Real.sqrt_nonneg (normSq y)
  nlinarith

theorem translated_inner_disk_subset (R : ℝ) (hR : 0 ≤ R) (x : Site)
    (hx : normSq x ≤ (R / 2) ^ 2) :
    translateFinset x (diskFinset (R / 2)) ⊆ diskFinset R := by
  intro z hz
  have hy : normSq (z - x) < (R / 2) ^ 2 := by
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hz
  have hh := normSq_add_lt_of_le_of_lt x (z - x) (by positivity : 0 ≤ R / 2)
    (by positivity : 0 ≤ R / 2) hx hy
  rw [show x + (z - x) = z by abel, show R / 2 + R / 2 = R by ring] at hh
  exact (mem_diskFinset _ _).mpr hh

theorem disk_subset_translated_outer (R : ℝ) (hR : 0 ≤ R) (x : Site)
    (hx : normSq x ≤ R ^ 2) :
    diskFinset R ⊆ translateFinset x (diskFinset (2 * R)) := by
  intro z hz
  have hxn : normSq (-x) ≤ R ^ 2 := by simpa only [normSq_neg] using hx
  have hz' : normSq z < R ^ 2 := (mem_diskFinset _ _).mp hz
  have hh := normSq_add_lt_of_le_of_lt (-x) z hR hR hxn hz'
  rw [show -x + z = z - x by abel, show R + R = 2 * R by ring] at hh
  exact (mem_translateFinset_iff x _ z).mpr ((mem_diskFinset _ _).mpr hh)

end SRWTightness
