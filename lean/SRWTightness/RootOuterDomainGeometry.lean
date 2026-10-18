import SRWTightness.GeneralEntranceRadialSupport
import SRWTightness.TranslatedDiskGeometry

namespace SRWTightness

/-- A one-step radial margin places both a root domain and all its exits inside the outer disk. -/
theorem root_domain_and_exit_inside (b : Site) (c R : ℝ) (hc : 0 ≤ c)
    (hfit : Real.sqrt (normSq b) + c + 1 < R) :
    translateFinset b (diskFinset c) ⊆ diskFinset R ∧
      domainExitBoundary (translateFinset b (diskFinset c)) ⊆ (diskFinset R : Set Site) := by
  have hb := Real.sqrt_nonneg (normSq b)
  have hR : 0 < R := by linarith
  have hbound : ∀ y : Site, normSq (y - b) ≤ (c + 1) ^ 2 → y ∈ diskFinset R := by
    intro y hy
    have hh := normSq_add_bound b (y - b) hb (by linarith : 0 ≤ c + 1)
      (le_of_eq (normSq_eq_sq_sqrt b)) hy
    rw [show b + (y - b) = y by abel] at hh
    apply (mem_diskFinset R y).mpr
    have hsq : (Real.sqrt (normSq b) + (c + 1)) ^ 2 < R ^ 2 :=
      (sq_lt_sq₀ (by positivity) hR.le).mpr (by linarith)
    exact hh.trans_lt hsq
  constructor
  · intro y hy
    have hy' : normSq (y - b) < c ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hy
    exact hbound y (by nlinarith)
  · intro y hy
    have hr := translated_disk_boundary_radial b c hc y hy
    have hs := Real.sq_sqrt (normSq_nonneg (y - b))
    have hn := Real.sqrt_nonneg (normSq (y - b))
    exact hbound y (by nlinarith)

end SRWTightness
