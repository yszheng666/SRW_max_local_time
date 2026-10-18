import SRWTightness.TranslatedDiskGeometry

namespace SRWTightness

/-- A ball with radial margins stays inside a translated annulus. -/
theorem lattice_ball_inside_annulus (b x : Site) (a B R : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hinner : a + B ≤ Real.sqrt (normSq (x - b)))
    (houter : Real.sqrt (normSq (x - b)) + B ≤ R) :
    translateFinset x (diskFinset B) ⊆
      translateFinset b (diskFinset R) \ translateFinset b (diskFinset a) := by
  intro y hy
  have hyB : normSq (y - x) < B ^ 2 := by
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hy
  have hx0 := Real.sqrt_nonneg (normSq (x - b))
  have hx2 := Real.sq_sqrt (normSq_nonneg (x - b))
  apply Finset.mem_sdiff.mpr
  constructor
  · have ht := normSq_add_lt_of_le_of_lt (x - b) (y - x) hx0 hB hx2.ge hyB
    rw [show (x - b) + (y - x) = y - b by abel] at ht
    apply (mem_translateFinset_iff b _ y).mpr
    apply (mem_diskFinset R (y - b)).mpr
    exact ht.trans_le ((sq_le_sq₀ (by positivity) (by linarith)).mpr houter)
  · intro hyA
    have hyA' : normSq (y - b) < a ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hyA
    have hxy : normSq (x - y) ≤ B ^ 2 := by
      simpa only [show x - y = -(y - x) by abel, normSq_neg] using hyB.le
    have ht := normSq_add_lt_of_le_of_lt (x - y) (y - b) hB ha hxy hyA'
    rw [show (x - y) + (y - b) = x - b by abel] at ht
    have hb := (sq_le_sq₀ (by positivity) hx0).mpr hinner
    nlinarith

end SRWTightness
