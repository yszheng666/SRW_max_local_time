import SRWTightness.AnnulusUniversalPayoff

namespace SRWTightness

/-- The logarithmic numerator error is uniform in the outer radius and starting point. -/
theorem annulus_log_numerator_universal (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (a R : ℝ) (ha : 2 ≤ a) (ha₀ : R₀ + 1 ≤ a) (haR : a ≤ R) (hCa : 4 * C ≤ (2 / Real.pi) * a)
    (x : Site) (hxl : a ^ 2 ≤ normSq x) (hxu : normSq x ≤ R ^ 2) :
    |annulusOuterExitProbability a R x * (Real.log R - Real.log a) -
      (Real.log (Real.sqrt (normSq x)) - Real.log a)| ≤
      4 / a := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < normSq x := by nlinarith
  have hroot : a ≤ Real.sqrt (normSq x) :=
    (Real.le_sqrt ha0.le (normSq_nonneg x)).mpr hxl
  have hp := hbound x (by linarith)
  have hg0 : 0 < (2 / Real.pi : ℝ) := by positivity
  have hdiv : C / normSq x ≤ (2 / Real.pi) / a := by
    apply (div_le_div_iff₀ hx0 ha0).mpr
    have h₁ := mul_le_mul_of_nonneg_right hCa ha0.le
    have h₂ := mul_le_mul_of_nonneg_left hxl hg0.le
    nlinarith
  have hp' := hp.trans hdiv
  have he := annulus_potential_exit_universal κ C R₀ hC hR₀ hbound
    a R ha ha₀ haR hCa x hxl hxu
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ hg).mp
  conv_lhs => rw [← abs_of_pos hg, ← abs_mul]
  apply abs_le.mpr
  have hpL := (abs_le.mp hp').1
  have hpU := (abs_le.mp hp').2
  have heL := (abs_le.mp he).1
  have heU := (abs_le.mp he).2
  have hs : (2 / Real.pi) / a + (3 * (2 / Real.pi)) / a =
      (4 / a) * (2 / Real.pi) := by ring
  constructor <;> nlinarith [hs]

end SRWTightness
