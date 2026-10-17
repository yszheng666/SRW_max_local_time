import SRWTightness.EquilibriumBoundarySupport
import SRWTightness.EquilibriumWeightBilinear
import SRWTightness.LatticeTranslation

namespace SRWTightness

theorem translated_disk_equilibrium_inner_zero (D : Finset Site) (b : Site) (a : ℝ) (ha : 2 ≤ a)
    (hKD : translateFinset b (diskFinset a) ⊆ D) (x : Site) (hx : normSq (x - b) < (a - 1) ^ 2) :
    equilibriumMeasure D (translateFinset b (diskFinset a)) x = 0 := by
  apply equilibriumMeasure_eq_zero_of_all_neighbors D _ hKD x
  intro d
  rw [mem_translateFinset_iff, mem_diskFinset]
  change normSq (x + step d - b) < a ^ 2
  have hs := Real.sq_sqrt (normSq_nonneg (x - b))
  have hr := Real.sqrt_nonneg (normSq (x - b))
  have hlt : Real.sqrt (normSq (x - b)) < a - 1 := by nlinarith
  have hb := normSq_step_le (x - b) d hr hs.ge
  rw [show x + step d - b = (x - b) + step d by abel]
  nlinarith

theorem translated_disk_equilibriumWeight_center_zero (D : Finset Site) (b : Site) (a : ℝ)
    (ha : 2 ≤ a) (hKD : translateFinset b (diskFinset a) ⊆ D) :
    equilibriumWeight D (translateFinset b (diskFinset a)) b = 0 := by
  have he := translated_disk_equilibrium_inner_zero D b a ha hKD b (by
    simp only [sub_self]
    norm_num [normSq]
    nlinarith)
  simp only [equilibriumWeight, he, zero_div]

/-- The one-step boundary shells of separated nested disks are disjoint. -/
theorem translated_disk_equilibriumWeight_disjoint (D : Finset Site) (b : Site) (a r : ℝ)
    (ha : 0 ≤ a) (hr : 2 ≤ r) (har : a ≤ r - 1)
    (hKD : translateFinset b (diskFinset r) ⊆ D) (x : Site) :
    equilibriumWeight D (translateFinset b (diskFinset a)) x *
      equilibriumWeight D (translateFinset b (diskFinset r)) x = 0 := by
  by_cases hx : x ∈ translateFinset b (diskFinset a)
  · have hn : normSq (x - b) < a ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hx
    have he := translated_disk_equilibrium_inner_zero D b r hr hKD x (by nlinarith)
    simp only [equilibriumWeight, he, zero_div, mul_zero]
  · rw [equilibriumWeight_zero_of_not_mem D _ x hx, zero_mul]

end SRWTightness
