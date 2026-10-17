import SRWTightness.DiskExitPotentialBound
import SRWTightness.DiskOnePoint

namespace SRWTightness

noncomputable def diskGreenAdditiveConstant : ℝ :=
  (2 / Real.pi) * Real.log 3 + potentialUpperConstant + potentialLowerConstant

theorem diskGreen_log_linear (R : ℝ) (hR : 1 ≤ R) (y : Site) (hy : y ∈ disk R) :
    diskGreen R 0 y ≤ (2 / Real.pi) * Real.log (R / max (Real.sqrt (normSq y)) 1) +
      diskGreenAdditiveConstant := by
  have hu := exitPayoff_potential_disk_upper R hR y hy
  have hl := potentialKernel_ge_log_radius y
  unfold diskGreen
  rw [potentialKernel_green_representation, zero_sub, potentialKernel_neg]
  have hR0 : 0 < R := by linarith
  have hrho : 0 < max (Real.sqrt (normSq y)) 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have he : Real.log ((3 * R) ^ 2) / Real.pi - (2 / Real.pi) * Real.log (max (Real.sqrt (normSq y)) 1) =
      (2 / Real.pi) * Real.log (R / max (Real.sqrt (normSq y)) 1) + (2 / Real.pi) * Real.log 3 := by
    rw [Real.log_pow, Real.log_mul (by norm_num) hR0.ne', Real.log_div hR0.ne' hrho.ne']
    ring
  unfold diskGreenAdditiveConstant
  linarith

theorem diskGreen_source_upper : ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ y ∈ disk R,
    diskGreen R 0 y ≤ C * (1 + Real.log (R / max (Real.sqrt (normSq y)) 1)) := by
  let C := diskGreenAdditiveConstant + 2 / Real.pi
  have hB : 0 < diskGreenAdditiveConstant := by
    unfold diskGreenAdditiveConstant
    have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hu := potentialUpperConstant_pos
    have hl := potentialLowerConstant_pos
    positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro R hR y hy
  have hR0 : 0 < R := by linarith
  have hrho : 0 < max (Real.sqrt (normSq y)) 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hsqrt : Real.sqrt (normSq y) ≤ R := (Real.sqrt_le_iff).mpr ⟨hR0.le, (show normSq y < R ^ 2 from hy).le⟩
  have hrat : 1 ≤ R / max (Real.sqrt (normSq y)) 1 := (le_div_iff₀ hrho).mpr (by simpa using max_le hsqrt hR)
  have hlog : 0 ≤ Real.log (R / max (Real.sqrt (normSq y)) 1) := Real.log_nonneg hrat
  refine (diskGreen_log_linear R hR y hy).trans ?_
  dsimp [C]
  nlinarith [mul_nonneg hB.le hlog, div_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos]

end SRWTightness
