import SRWTightness.PotentialUnitRadiusUniversal
import SRWTightness.AnnulusExitGeometry

namespace SRWTightness

/-- Fine potential control on the actual inner and outer exit boundaries. -/
theorem annulus_exit_potential_universal (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (a R : ℝ) (ha : 2 ≤ a) (ha₀ : R₀ + 1 ≤ a) (haR : a ≤ R) (hCa : 4 * C ≤ (2 / Real.pi) * a)
    (x : Site) (hxl : a ^ 2 ≤ normSq x) (hxu : normSq x ≤ R ^ 2)
    (y : Site) (hy : y ∈ domainExitRange (annulusFinset a R) x)
    (hyD : y ∉ annulusFinset a R) :
    |potentialKernel y - ((2 / Real.pi) * Real.log a + κ +
      ((2 / Real.pi) * (Real.log R - Real.log a)) *
        (if y ∉ diskFinset R then 1 else 0))| ≤
      (3 * (2 / Real.pi)) / a := by
  have ha0 : 0 < a := by linarith
  have hR0 : 0 < R := by linarith
  by_cases hyR : y ∉ diskFinset R
  · have hylo : R ^ 2 ≤ normSq y := by
      simpa only [mem_diskFinset, disk, Set.mem_setOf_eq, not_lt] using hyR
    have hh := potential_unit_radius_universal κ C R₀ hC hR₀ hbound R
      (by linarith) (by linarith)
      (hCa.trans (mul_le_mul_of_nonneg_left haR (by positivity))) y
      (by nlinarith) (annulusExitRange_normSq_upper a R hR0.le x hxu y hy)
    have hd : (3 * (2 / Real.pi)) / R ≤
        (3 * (2 / Real.pi)) / a :=
      div_le_div_of_nonneg_left (by positivity) ha0 haR
    simp only [if_pos hyR, mul_one]
    have he : (2 / Real.pi) * Real.log a + κ +
        (2 / Real.pi) * (Real.log R - Real.log a) = (2 / Real.pi) * Real.log R + κ := by ring
    rw [he]
    exact hh.trans hd
  · have hyin : y ∈ diskFinset R := by simpa using hyR
    have hyinner : y ∈ diskFinset a := by
      by_contra hn
      exact hyD (Finset.mem_sdiff.mpr ⟨hyin, hn⟩)
    have hysq : normSq y < a ^ 2 := by
      simpa only [mem_diskFinset, disk, Set.mem_setOf_eq] using hyinner
    simp only [if_neg hyR, mul_zero, add_zero]
    exact potential_unit_radius_universal κ C R₀ hC hR₀ hbound a ha ha₀ hCa y
      (annulusExitRange_normSq_lower a R (by linarith) x hxl y hy) (by nlinarith)

end SRWTightness
