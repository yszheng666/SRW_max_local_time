import SRWTightness.TranslatedRadialPerturbation

namespace SRWTightness

/-- A short outer exit is separated from its own inner disk by the annular gap. -/
theorem disk_exit_inner_separation (b x y : Site) (R a : ℝ) (hR : 0 ≤ R)
    (ha : 0 ≤ a) (hx : x ∈ domainExitBoundary (translateFinset b (diskFinset R)))
    (hy : y ∈ translateFinset b (diskFinset a)) :
    R - a ≤ Real.sqrt (normSq (y - x)) := by
  have hr := translated_disk_boundary_radial b R hR x hx
  have hy' : normSq (y - b) < a ^ 2 := by
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hy
  have hyr : Real.sqrt (normSq (y - b)) ≤ a :=
    (Real.sqrt_le_iff).mpr ⟨ha, hy'.le⟩
  have hp := (abs_le.mp (lattice_radius_sub_perturbation x y b)).1
  rw [show y - x = -(x - y) by abel, normSq_neg]
  linarith [hr.1]

/-- An exit of one outer disk is separated from the other inner disk by center distance. -/
theorem disk_exit_other_inner_separation (b w x y : Site) (R a : ℝ) (hR : 0 ≤ R)
    (ha : 0 ≤ a) (hx : x ∈ domainExitBoundary (translateFinset b (diskFinset R)))
    (hy : y ∈ translateFinset w (diskFinset a)) :
    Real.sqrt (normSq (w - b)) - (R + 1) - a ≤ Real.sqrt (normSq (y - x)) := by
  have hr := translated_disk_boundary_radial b R hR x hx
  have hy' : normSq (y - w) < a ^ 2 := by
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hy
  have hyr : Real.sqrt (normSq (y - w)) ≤ a :=
    (Real.sqrt_le_iff).mpr ⟨ha, hy'.le⟩
  have h₁ := lattice_radius_add_le (w - y) (y - x)
  have h₂ := lattice_radius_add_le (w - x) (x - b)
  rw [show w - y + (y - x) = w - x by abel,
    show w - y = -(y - w) by abel, normSq_neg] at h₁
  rw [show w - x + (x - b) = w - b by abel] at h₂
  linarith [hr.2]

end SRWTightness
