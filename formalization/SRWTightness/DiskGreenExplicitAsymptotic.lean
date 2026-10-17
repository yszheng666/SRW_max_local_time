import SRWTightness.PotentialExplicitAsymptotic
import SRWTightness.DiskDiagonalFineAsymptotic

open Filter
open scoped Topology
namespace SRWTightness

/-- Source (2.7) has the explicit manuscript constant and an inverse-radius remainder. -/
theorem diskGreen_explicit_asymptotic (hinput : PotentialKernelAsymptoticInput) :
    ∃ B R₁ : ℝ, 0 ≤ B ∧ 2 ≤ R₁ ∧
      (∀ R : ℝ, R₁ ≤ R →
        |diskGreen R 0 0 - ((2 / Real.pi) * Real.log R + sourcePotentialConstant)| ≤ B / R) ∧
      Tendsto (fun R : ℝ ↦ diskGreen R 0 0 - ((2 / Real.pi) * Real.log R + sourcePotentialConstant))
        atTop (𝓝 0) := by
  obtain ⟨C, R₀, hC, hR₀, hb⟩ := potentialKernel_explicit_asymptotic hinput
  let B : ℝ := 4 * C + 2 * (2 / Real.pi)
  let R₁ : ℝ := max 2 (R₀ + 1)
  have herr : ∀ R : ℝ, R₁ ≤ R →
      |diskGreen R 0 0 - ((2 / Real.pi) * Real.log R + sourcePotentialConstant)| ≤ B / R := by
    intro R hR
    exact diskGreen_origin_fine_bound sourcePotentialConstant C R₀ hC hR₀ hb R
      ((le_max_left _ _).trans hR) ((le_max_right _ _).trans hR)
  refine ⟨B, R₁, by dsimp [B]; positivity, le_max_left _ _, herr, ?_⟩
  have hlim : Tendsto (fun R : ℝ ↦ B / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)).const_mul B
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop R₁] with R hR
  simpa only [Real.norm_eq_abs] using herr R hR

end SRWTightness
