import SRWTightness.AnnulusFineLogarithm
import SRWTightness.LogRadiusPerturbation

namespace SRWTightness

/-- Uniform logarithmic spacing converts the actual annulus estimate into a half-probability bound. -/
theorem annulus_half_of_log_radius_bounds (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (a R : ℝ) (ha : 2 ≤ a) (ha₀ : R₀ + 1 ≤ a) (haR : a ≤ R)
    (x : Site) (hxl : a ^ 2 ≤ normSq x) (hxu : normSq x ≤ R ^ 2)
    (l δ : ℝ) (hδ : δ ≤ 1 / 2)
    (hla : |Real.log a - l| ≤ δ)
    (hlx : |Real.log (Real.sqrt (normSq x)) - (l + 1)| ≤ δ)
    (hlR : |Real.log R - (l + 2)| ≤ δ) :
    |annulusOuterExitProbability a R x - 1 / 2| ≤
      ((5 * C + 2 * (2 / Real.pi)) / a) / (2 / Real.pi) + 2 * δ := by
  have haL := (abs_le.mp hla).1
  have haU := (abs_le.mp hla).2
  have hxL := (abs_le.mp hlx).1
  have hxU := (abs_le.mp hlx).2
  have hRL := (abs_le.mp hlR).1
  have hRU := (abs_le.mp hlR).2
  apply probability_half_of_log_errors (annulusOuterExitProbability a R x)
    (Real.log R - Real.log a) (Real.log (Real.sqrt (normSq x)) - Real.log a)
  · linarith
  · exact annulus_log_numerator_error κ C R₀ hC hR₀ hbound a R ha ha₀ haR x hxl hxu
  · apply abs_le.mpr
    constructor <;> linarith

end SRWTightness
