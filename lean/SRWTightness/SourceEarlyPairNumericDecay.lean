import SRWTightness.SourceEarlyPairExponent
import SRWTightness.SourceEarlyLogAbsorption

open Filter
namespace SRWTightness

/-- The complete counted early-pair bound has uniform stretched-exponential decay. -/
theorem source_early_pair_numeric_decay (K C : ℝ) (hK : 0 < K) (hC : 0 ≤ C)
    (J₀ : ℕ) :
    ∃ a₀ : ℕ, 2 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ a : ℕ, a₀ ≤ a →
      a < sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
      K * ((ν : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 * Real.exp
        (-2 * (a : ℝ) - 4 * (ν : ℝ) - b ^ 2 / (2 * ((j : ℝ) + 1)) +
          4 * b + C * ((J : ℝ) + 1)) ≤ Real.exp (-(a : ℝ) ^ (2 / 5 : ℝ) / 2) := by
  obtain ⟨ap, hap, hp⟩ := source_early_log_prefactor_absorption K C hK hC J₀
  obtain ⟨al, hl⟩ := source_early_distance_levels J₀
  refine ⟨max ap al, hap.trans (le_max_left _ _), ?_⟩
  filter_upwards [hl, source_early_pair_exponent_upper] with t hl he
  intro a ha hrange
  dsimp only
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
  let w := (j : ℝ) ^ (2 / 5 : ℝ)
  let P := K * ((ν : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2
  have hlevels := hl a ((le_max_right _ _).trans ha) hrange
  have hJa : J ≤ a := by have hh := hlevels.1; dsimp only [j, J] at *; omega
  have hjmax : j ≤ 2 * sourceCoarseLowerLevel t := by
    have hh := hlevels.2.2
    dsimp only [j, ν] at *
    omega
  have hbase := he a J hJa hjmax
  change -2 * (a : ℝ) - 4 * (ν : ℝ) - b ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * b ≤
    -2 * w - 10 * (J : ℝ) - 10 at hbase
  have hbase' : -2 * (a : ℝ) - 4 * (ν : ℝ) -
      b ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * b ≤ -2 * w := by
    linarith only [hbase, (Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have hpref := hp a ((le_max_left _ _).trans ha)
  change P * Real.exp (C * ((J : ℝ) + 1)) ≤ Real.exp w at hpref
  have hpower : (a : ℝ) ^ (2 / 5 : ℝ) ≤ 2 * w := by
    have hh := hlevels.2.1
    have hr := Real.rpow_le_rpow (Nat.cast_nonneg a)
      (show (a : ℝ) ≤ 2 * (j : ℝ) by linarith only [hh])
      (by norm_num : (0 : ℝ) ≤ 2 / 5)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg j)] at hr
    have h2 := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (2 / 5 : ℝ) ≤ 1)
    rw [Real.rpow_one] at h2
    exact hr.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (Nat.cast_nonneg j) _))
  calc
    _ = (P * Real.exp (C * ((J : ℝ) + 1))) * Real.exp
        (-2 * (a : ℝ) - 4 * (ν : ℝ) - b ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * b) := by
      change P * Real.exp
        ((-2 * (a : ℝ) - 4 * (ν : ℝ) - b ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * b) +
          C * ((J : ℝ) + 1)) = _
      rw [Real.exp_add]
      ring
    _ ≤ (P * Real.exp (C * ((J : ℝ) + 1))) * Real.exp (-2 * w) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbase') (by dsimp only [P]; positivity)
    _ ≤ Real.exp w * Real.exp (-2 * w) :=
      mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ = Real.exp (-w) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hpower])

end SRWTightness
