import SRWTightness.ExternalPotentialAsymptotic
import SRWTightness.LogRadiusOvershoot
import SRWTightness.PotentialRadiusComparison

namespace SRWTightness

/-- Fine potential asymptotics control both sides of a one-step radial overshoot. -/
theorem potential_kernel_unit_radius_bound (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (a : ℝ) (ha : 2 ≤ a) (ha₀ : R₀ + 1 ≤ a) (z : Site)
    (hzl : (a - 1) ^ 2 ≤ normSq z) (hzu : normSq z ≤ (a + 1) ^ 2) :
    |potentialKernel z - ((2 / Real.pi) * Real.log a + κ)| ≤
      (4 * C + 2 * (2 / Real.pi)) / a := by
  have ha0 : 0 < a := by linarith
  have hrlo : a - 1 ≤ Real.sqrt (normSq z) :=
    (Real.le_sqrt (by linarith) (normSq_nonneg z)).mpr hzl
  have hrhi : Real.sqrt (normSq z) ≤ a + 1 :=
    (Real.sqrt_le_left (by linarith)).mpr hzu
  have hz0 : 0 < normSq z := by nlinarith
  have hfour : a ≤ 4 * normSq z := by nlinarith [sq_nonneg (a - 2)]
  have hdiv : C / normSq z ≤ (4 * C) / a := by
    apply (div_le_div_iff₀ hz0 ha0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hfour hC]
  have hlog := log_radius_unit_error (Real.sqrt (normSq z)) a ha hrlo hrhi
  have hp := hbound z (by linarith)
  have hg : 0 ≤ (2 / Real.pi : ℝ) := by positivity
  calc
    _ = |(potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)) +
        (2 / Real.pi) * (Real.log (Real.sqrt (normSq z)) - Real.log a)| := by
      congr 1
      ring
    _ ≤ |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| +
        |(2 / Real.pi) * (Real.log (Real.sqrt (normSq z)) - Real.log a)| := abs_add_le _ _
    _ ≤ (4 * C) / a + (2 / Real.pi) * (2 / a) := by
      rw [abs_mul, abs_of_nonneg hg]
      exact add_le_add (hp.trans hdiv) (mul_le_mul_of_nonneg_left hlog hg)
    _ = _ := by ring

end SRWTightness
