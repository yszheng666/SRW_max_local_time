import SRWTightness.PotentialKernelUnitRadius

namespace SRWTightness

/-- At large radii, the one-step error has a universal leading coefficient. -/
theorem potential_unit_radius_universal (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤
        C / normSq z)
    (a : ℝ) (ha : 2 ≤ a) (ha₀ : R₀ + 1 ≤ a) (hCa : 4 * C ≤ (2 / Real.pi) * a)
    (z : Site) (hzl : (a - 1) ^ 2 ≤ normSq z) (hzu : normSq z ≤ (a + 1) ^ 2) :
    |potentialKernel z - ((2 / Real.pi) * Real.log a + κ)| ≤
      3 * (2 / Real.pi) / a := by
  have ha0 : 0 < a := by linarith
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hrlo : a - 1 ≤ Real.sqrt (normSq z) :=
    (Real.le_sqrt (by linarith) (normSq_nonneg z)).mpr hzl
  have hrhi : Real.sqrt (normSq z) ≤ a + 1 :=
    (Real.sqrt_le_left (by linarith)).mpr hzu
  have hz0 : 0 < normSq z := by nlinarith
  have hfour : a ^ 2 ≤ 4 * normSq z := by nlinarith [sq_nonneg (a - 2)]
  have hdiv : C / normSq z ≤ (2 / Real.pi) / a := by
    apply (div_le_div_iff₀ hz0 ha0).mpr
    have h₁ := mul_le_mul_of_nonneg_right hCa ha0.le
    have h₂ := mul_le_mul_of_nonneg_left hfour hg.le
    nlinarith
  have hlog := log_radius_unit_error (Real.sqrt (normSq z)) a ha hrlo hrhi
  have hp := hbound z (by linarith)
  calc
    _ = |(potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)) +
        (2 / Real.pi) * (Real.log (Real.sqrt (normSq z)) - Real.log a)| := by
      congr 1
      ring
    _ ≤ |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| +
        |(2 / Real.pi) * (Real.log (Real.sqrt (normSq z)) - Real.log a)| := abs_add_le _ _
    _ ≤ (2 / Real.pi) / a + (2 / Real.pi) * (2 / a) := by
      rw [abs_mul, abs_of_nonneg hg.le]
      exact add_le_add (hp.trans hdiv) (mul_le_mul_of_nonneg_left hlog hg.le)
    _ = _ := by ring

end SRWTightness
