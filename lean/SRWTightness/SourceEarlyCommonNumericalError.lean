import SRWTightness.SourceEarlyLevelBounds
import SRWTightness.SourceEarlyGapWeight
import SRWTightness.SourceCommonPairRadiusLower
import SRWTightness.SourceLongEscapeProbability

open Filter
namespace SRWTightness

/-- Equation 8.12's numerical majorant at the actual distance-dependent common level. The
inverse-radius contribution vanishes uniformly and the logarithmic-gap contribution is bounded. -/
theorem source_early_common_numerical_error (J₀ : ℕ) :
    ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ a : ℕ, a₀ ≤ a →
      a < sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      ((j : ℝ) + 1) ^ 2 * (14 / sourceCommonPairInnerRadius t j +
        ((J : ℝ) + 1) * Real.exp (-(J : ℝ))) ≤ 56 / t ^ 5 + 1 ∧
      56 / t ^ 5 + 1 ≤ 57 := by
  obtain ⟨a₀, ha₀, hgap⟩ := source_early_distance_gap_small J₀
  obtain ⟨a₁, hlevels⟩ := source_early_distance_levels J₀
  refine ⟨max a₀ a₁, ha₀.trans (le_max_left _ _), ?_⟩
  filter_upwards [source_early_level_bounds, hlevels,
    eventually_ge_atTop (sourceScaleThreshold 4)] with t ht hlevels hscale
  intro a ha hrange
  dsimp only
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  have hJ : J ≤ a := by have hh := hgap a ((le_max_left _ _).trans ha); omega
  have hν := (hlevels a ((le_max_right _ _).trans ha) hrange).2.2
  have hj : j ≤ 2 * sourceCoarseLowerLevel t := by dsimp [j]; omega
  have hjt := (ht.2 j hj).2.1
  have hr := sourceCommonPairInnerRadius_ge_lower t j (ht.2 j hj).1
  have hr0 := sourceCommonPairInnerRadius_pos t j
  have hm := sourceLowerRadius_pos t
  have ht0 : 0 < t := by linarith [ht.1]
  have hsq : ((j : ℝ) + 1) ^ 2 ≤ 4 * t ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (j : ℝ) + 1)
      (show (j : ℝ) + 1 ≤ 2 * t by linarith [ht.1]) 2
    nlinarith only [hh]
  have hmajor : t ^ 2 / sourceLowerRadius t ≤ 1 / t ^ 5 := by
    have hh := div_le_div_of_nonneg_left (sq_nonneg t) (pow_pos ht0 7)
      (sourceLowerRadius_ge_seventh_power t hscale)
    exact hh.trans_eq (by field_simp [ht0.ne'])
  have hreturn : ((j : ℝ) + 1) ^ 2 * (14 / sourceCommonPairInnerRadius t j) ≤
      56 / t ^ 5 := by
    calc
      _ ≤ (4 * t ^ 2) * (14 / sourceCommonPairInnerRadius t j) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
      _ ≤ (4 * t ^ 2) * (14 / sourceLowerRadius t) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num) hm hr)
          (by positivity)
      _ = 56 * (t ^ 2 / sourceLowerRadius t) := by ring
      _ ≤ 56 * (1 / t ^ 5) := mul_le_mul_of_nonneg_left hmajor (by norm_num)
      _ = _ := by ring
  have hja : (j : ℝ) ≤ a := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hsqA : ((j : ℝ) + 1) ^ 2 ≤ ((a : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hweight : ((j : ℝ) + 1) ^ 2 * (((J : ℝ) + 1) * Real.exp (-(J : ℝ))) ≤ 1 := by
    calc
      _ ≤ ((a : ℝ) + 1) ^ 2 * (((J : ℝ) + 1) * Real.exp (-(J : ℝ))) :=
        mul_le_mul_of_nonneg_right hsqA (by positivity)
      _ ≤ 1 := by simpa only [mul_assoc] using source_early_gap_weight a J₀ hJ
  constructor
  · nlinarith only [hreturn, hweight]
  · have ht5 : 1 ≤ t ^ 5 := one_le_pow₀ (by linarith [ht.1])
    have hh := div_le_self (by norm_num : (0 : ℝ) ≤ 56) ht5
    linarith

end SRWTightness
