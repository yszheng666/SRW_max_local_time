import SRWTightness.PotentialKernelUnitRadius
import SRWTightness.LogRadiusPerturbation

namespace SRWTightness

/-- Fine potential asymptotics remain uniform under a bounded relative radial perturbation. -/
theorem potential_kernel_radial_perturbation (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (R A : ℝ) (hR : 0 < R) (hA : 0 ≤ A) (hAR : 2 * A ≤ R) (hlarge : R₀ ≤ R - A)
    (z : Site) (hlo : R - A ≤ Real.sqrt (normSq z))
    (hhi : Real.sqrt (normSq z) ≤ R + A) :
    |potentialKernel z - ((2 / Real.pi) * Real.log R + κ)| ≤
      4 * C / R ^ 2 + (2 / Real.pi) * (2 * A / R) := by
  have hs := Real.sq_sqrt (normSq_nonneg z)
  have hr : 0 < Real.sqrt (normSq z) := by linarith
  have hn : 0 < normSq z := by nlinarith
  have hfour : R ^ 2 ≤ 4 * normSq z := by nlinarith
  have hd : C / normSq z ≤ 4 * C / R ^ 2 := by
    apply (div_le_div_iff₀ hn (sq_pos_of_pos hR)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hfour hC]
  have hp := hbound z (hlarge.trans hlo)
  have hl : |Real.log (Real.sqrt (normSq z)) - Real.log R| ≤ 2 * A / R := by
    by_cases hA0 : A = 0
    · have he : Real.sqrt (normSq z) = R := by subst A; linarith
      simp [hA0, he]
    · exact log_radius_perturbation _ R A (lt_of_le_of_ne hA (Ne.symm hA0)) hAR hlo hhi
  have hg : 0 ≤ (2 / Real.pi : ℝ) := by positivity
  calc
    _ = |(potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)) +
        (2 / Real.pi) * (Real.log (Real.sqrt (normSq z)) - Real.log R)| := by
      congr 1
      ring
    _ ≤ |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| +
        |(2 / Real.pi) * (Real.log (Real.sqrt (normSq z)) - Real.log R)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hg]
      exact add_le_add (hp.trans hd) (mul_le_mul_of_nonneg_left hl hg)

end SRWTightness
