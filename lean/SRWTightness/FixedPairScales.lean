import SRWTightness.SourceCommonPairCoarseReferenceSum

open Filter
namespace SRWTightness

/-- Every fixed continuation level is eventually below the source coarse cutoff. -/
theorem sourceCoarseLowerLevel_eventually_ge (N : ℕ) :
    ∀ᶠ t : ℝ in atTop, N ≤ sourceCoarseLowerLevel t := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (N : ℝ)))] with t ht
  have hlog : 1 ≤ Real.log t := (le_max_left _ _).trans ht
  have hN : (N : ℝ) ≤ Real.log t := (le_max_right _ _).trans ht
  have hx : 1 ≤ 1000 * Real.log t := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 : ℝ) ≤ 5 / 2)
  rw [Real.rpow_one] at hp
  have hc := Nat.le_ceil ((1000 * Real.log t) ^ (5 / 2 : ℝ))
  have hn : (N : ℝ) ≤ (sourceCoarseLowerLevel t : ℝ) := by
    change (N : ℝ) ≤ (⌈(1000 * Real.log t) ^ (5 / 2 : ℝ)⌉₊ : ℝ)
    linarith
  exact_mod_cast hn

/-- A single level handles every bounded distance index by a bounded, sufficiently large gap. -/
theorem fixed_pair_level_gap (a₀ J₀ a : ℕ) (ha : a ≤ a₀) :
    let ν := a₀ + J₀ + 5
    let J := ν - a - 5
    ν = a + J + 5 ∧ J₀ ≤ J ∧ J ≤ ν := by
  dsimp only
  omega

end SRWTightness
