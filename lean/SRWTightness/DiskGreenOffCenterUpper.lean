import SRWTightness.DiskDiagonalLogBound
import SRWTightness.DiskGreenLogBound

namespace SRWTightness

/-- A uniform logarithmic Green bound with arbitrary interior starting point. -/
theorem diskGreen_off_center_upper (R : ℝ) (hR : 1 ≤ R) (x y : Site)
    (hx : x ∈ disk R) (hy : y ∈ disk R) :
    diskGreen R x y ≤
      (2 / Real.pi) * Real.log (2 * R / max (Real.sqrt (normSq (y - x))) 1) +
        diskGreenAdditiveConstant := by
  have hsub := disk_subset_translated_outer R (by linarith) x
    (show normSq x ≤ R ^ 2 from (show normSq x < R ^ 2 from hx).le)
  have hm := killedGreen_mono_domain _ _ hsub x y
  have he := killedGreen_translate x (diskFinset (2 * R)) 0 (y - x)
  simp only [add_zero, add_sub_cancel] at he
  rw [he] at hm
  have hy' : y - x ∈ disk (2 * R) := by
    have hh := hsub ((mem_diskFinset R y).mpr hy)
    simpa only [mem_translateFinset_iff, mem_diskFinset] using hh
  exact hm.trans (diskGreen_log_linear (2 * R) (by linarith) (y - x) hy')

/-- The off-center bound is invariant under translation of the killing disk. -/
theorem translated_disk_green_off_center_upper (b x y : Site) (R : ℝ) (hR : 1 ≤ R)
    (hx : x ∈ translateFinset b (diskFinset R))
    (hy : y ∈ translateFinset b (diskFinset R)) :
    killedGreen (translateFinset b (diskFinset R)) x y ≤
      (2 / Real.pi) * Real.log (2 * R / max (Real.sqrt (normSq (y - x))) 1) +
        diskGreenAdditiveConstant := by
  have hh := diskGreen_off_center_upper R hR (x - b) (y - b)
    (by simpa only [mem_translateFinset_iff, mem_diskFinset] using hx)
    (by simpa only [mem_translateFinset_iff, mem_diskFinset] using hy)
  have he := killedGreen_translate b (diskFinset R) (x - b) (y - b)
  simp only [add_sub_cancel] at he
  rw [he]
  simpa only [diskGreen, show y - b - (x - b) = y - x by abel] using hh

end SRWTightness
