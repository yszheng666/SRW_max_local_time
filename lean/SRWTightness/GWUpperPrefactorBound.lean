import SRWTightness.ExternalGWBarrier
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SRWTightness

/-- The square-root branching factor has the manuscript quarter-power population scale. -/
theorem gw_upper_sqrt_factor (J L u : ℝ) (hJ : 0 ≤ J) (hL : 0 < L)
    (hu : L / 2 ≤ u) :
    Real.sqrt (Real.sqrt (2 * J) / (u * L)) ≤ 2 * J ^ (1 / 4 : ℝ) / L := by
  have hu0 : 0 < u := by linarith
  have hr := Real.rpow_nonneg hJ (1 / 4 : ℝ)
  have hr2 : (J ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt J := by
    rw [← Real.rpow_two, ← Real.rpow_mul hJ, Real.sqrt_eq_rpow]
    norm_num
  have hx : Real.sqrt (2 * J) ≤ 2 * (J ^ (1 / 4 : ℝ)) ^ 2 := by
    rw [hr2]
    nlinarith [Real.sq_sqrt hJ, Real.sq_sqrt (show 0 ≤ 2 * J by positivity),
      Real.sqrt_nonneg J, Real.sqrt_nonneg (2 * J)]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ 2 * (J ^ (1 / 4 : ℝ)) ^ 2 / (u * L) :=
      div_le_div_of_nonneg_right hx (by positivity)
    _ ≤ 4 * (J ^ (1 / 4 : ℝ)) ^ 2 / L ^ 2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left hu
        (show 0 ≤ 4 * (J ^ (1 / 4 : ℝ)) ^ 2 * L by positivity)
      nlinarith
    _ = _ := by ring

/-- Dropping the nonpositive initial square yields the source exponential factor. -/
theorem gw_upper_exponential_bound (x u L : ℝ) (hL : 0 < L) :
    Real.exp (-((x - u) ^ 2 / (2 * L))) ≤
      Real.exp (-u ^ 2 / (2 * L) + (u / L) * x) := by
  apply Real.exp_le_exp.mpr
  have he : -((x - u) ^ 2 / (2 * L)) =
      -u ^ 2 / (2 * L) + (u / L) * x - x ^ 2 / (2 * L) := by ring
  rw [he]
  have hn : 0 ≤ x ^ 2 / (2 * L) := by positivity
  linarith

/-- A bounded initial margin gives the exact quarter-power over squared-depth prefactor. -/
theorem gw_upper_prefactor_bound (L : ℕ) (J u a b M : ℝ) (hL : 0 < L)
    (hJ : 0 ≤ J) (hu : (L : ℝ) / 2 ≤ u)
    (hA : 0 ≤ 1 + a - Real.sqrt (2 * J))
    (hAM : 1 + a - Real.sqrt (2 * J) ≤ M) (hS : 0 ≤ 1 + b - u) :
    gwBarrierPrefactor L (Real.sqrt (2 * J)) u a b *
      Real.sqrt (Real.sqrt (2 * J) / (u * L)) ≤
        2 * M * (1 + b - u) / (L : ℝ) ^ 2 * J ^ (1 / 4 : ℝ) *
          Real.exp (-u ^ 2 / (2 * L) + (u / L) * Real.sqrt (2 * J)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hM : 0 ≤ M := hA.trans hAM
  have hm : (1 + a - Real.sqrt (2 * J)) * (1 + b - u) / L ≤
      M * (1 + b - u) / L :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAM hS) hL0.le
  unfold gwBarrierPrefactor
  calc
    _ ≤ (M * (1 + b - u) / L) *
        Real.exp (-u ^ 2 / (2 * L) + (u / L) * Real.sqrt (2 * J)) *
          (2 * J ^ (1 / 4 : ℝ) / L) :=
      mul_le_mul (mul_le_mul hm (gw_upper_exponential_bound _ _ _ hL0)
        (Real.exp_pos _).le (by positivity))
        (gw_upper_sqrt_factor J L u hJ hL0 hu) (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

end SRWTightness
