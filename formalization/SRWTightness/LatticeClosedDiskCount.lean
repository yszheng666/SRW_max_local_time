import SRWTightness.LatticeMeshCardinality

namespace SRWTightness

/-- Finite lattice subsets of a closed disk, including the origin, have a quadratic count. -/
theorem lattice_closed_disk_count (r : ℝ) (hr : 1 ≤ r) (Z : Finset Site)
    (hZ : ∀ z ∈ Z, Real.sqrt (normSq z) ≤ r) :
    (Z.card : ℝ) ≤ 101 * r ^ 2 := by
  classical
  have hr0 : 0 < r := by linarith
  have hcount := lattice_mesh_cardinality (2 * r) (by positivity) 1 (by norm_num)
    (Z.erase 0) (Finset.notMem_erase _ _) (by
      intro z hz
      have hn := hZ z (Finset.mem_of_mem_erase hz)
      refine ⟨?_, by simp, by simp⟩
      apply (mem_diskFinset _ _).mpr
      change normSq z < (2 * r) ^ 2
      nlinarith [Real.sq_sqrt (normSq_nonneg z), Real.sqrt_nonneg (normSq z)])
  have hcount' : ((Z.erase 0).card : ℝ) ≤ 100 * r ^ 2 := by
    convert hcount using 1 <;> norm_num <;> ring
  have hcard : (Z.card : ℝ) ≤ ((Z.erase 0).card : ℝ) + 1 := by
    by_cases hz : (0 : Site) ∈ Z
    · have hh := Finset.card_erase_add_one hz
      exact_mod_cast (le_of_eq hh.symm)
    · rw [Finset.erase_eq_of_notMem hz]
      linarith
  nlinarith [sq_nonneg (r - 1)]

end SRWTightness
