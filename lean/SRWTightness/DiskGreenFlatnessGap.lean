import SRWTightness.GreenRadialGap
import SRWTightness.TranslatedRadialPerturbation

namespace SRWTightness

/-- Actual translated disk Green flatness for a unit entrance layer and nearby observations. -/
theorem translated_disk_green_flatness_gap (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (b x y : Site) (R r a : ℝ) (ha : 0 ≤ a) (hsep : r + 1 < R)
    (hRl : R₀ ≤ R - (a + 1)) (hrl : R₀ ≤ r - (a + 1))
    (hx : r - 1 ≤ Real.sqrt (normSq (x - b)) ∧ Real.sqrt (normSq (x - b)) ≤ r + 1)
    (hy : Real.sqrt (normSq (y - b)) ≤ a) :
    |killedGreen (translateFinset b (diskFinset R)) x y -
        (2 / Real.pi) * (Real.log R - Real.log r)| ≤
      (C / (R - (a + 1)) ^ 2 + (2 / Real.pi) * ((a + 1) / (R - (a + 1)))) +
      (C / (r - (a + 1)) ^ 2 + (2 / Real.pi) * ((a + 1) / (r - (a + 1)))) := by
  have hR : 0 < R := by linarith
  have hr : 0 < r := by linarith
  have hxD : x ∈ translateFinset b (diskFinset R) := by
    simp only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq]
    have hs := Real.sq_sqrt (normSq_nonneg (x - b))
    have hn := Real.sqrt_nonneg (normSq (x - b))
    nlinarith [hx.2]
  apply green_flatness_radial_gap κ C R₀ hC hR₀ hbound _ x y hxD
    R r (a + 1) (a + 1) hR hr (by linarith) (by linarith) hRl hrl
  · intro z hz
    exact translated_disk_boundary_distance b y R a hR.le hy z hz
  · have hp := abs_le.mp (lattice_radius_sub_perturbation x y b)
    constructor <;> linarith [hx.1, hx.2]

end SRWTightness
