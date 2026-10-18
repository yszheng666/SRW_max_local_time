import SRWTightness.EarlyEndpointMonotonicity
import SRWTightness.SourceEarlyLevelBounds
import SRWTightness.SourceCommonBarrierSlope

open Filter
namespace SRWTightness

/-- After spatial counting, the original early exponent retains its stretched-power deficit. -/
theorem source_early_pair_exponent_upper :
    ∀ᶠ t : ℝ in atTop, ∀ a J : ℕ, J ≤ a → a - J ≤ 2 * sourceCoarseLowerLevel t →
      let j := a - J
      let ν := a + J + 5
      let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ);
      -2 * (a : ℝ) - 4 * (ν : ℝ) - b ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * b ≤
        -2 * (j : ℝ) ^ (2 / 5 : ℝ) - 10 * (J : ℝ) - 10 := by
  filter_upwards [source_early_level_bounds, source_common_barrier_slope] with t hl hs
  intro a J hJ hj
  dsimp only
  let j := a - J
  let w := (j : ℝ) ^ (2 / 5 : ℝ)
  let b := 4 + sourceBarrierSlope t * j - w
  let c := 2 * (j : ℝ) - w + 4
  have hθ := (hs j (hl.2 j hj).1).2.1
  have hw : 0 ≤ w := Real.rpow_nonneg (Nat.cast_nonneg j) _
  have hbc : b ≤ c := by
    have hh := mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg j)
    dsimp only [b, c]
    linarith only [hh]
  have hc : c ≤ 4 * ((j : ℝ) + 1) := by
    dsimp only [c]
    linarith only [hw, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hq := early_endpoint_quadratic_mono ((j : ℝ) + 1) b c (by positivity) hbc hc
  change -b ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * b ≤
    -(2 * (j : ℝ) - w + 4) ^ 2 / (2 * ((j : ℝ) + 1)) +
      4 * (2 * (j : ℝ) - w + 4) at hq
  rw [source_early_endpoint_quadratic_identity] at hq
  have hr : 0 ≤ (w - 2) ^ 2 / (2 * ((j : ℝ) + 1)) := by positivity
  have he := early_distance_exponent_cancellation a J hJ
  change -2 * (a : ℝ) - 4 * ((a + J + 5 : ℕ) : ℝ) -
    b ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * b ≤ -2 * w - 10 * (J : ℝ) - 10
  change -2 * (a : ℝ) - 4 * ((a + J + 5 : ℕ) : ℝ) + 6 * (j : ℝ) =
    -10 * (J : ℝ) - 20 at he
  have hq' := hq.trans (sub_le_self _ hr)
  calc
    _ = (-2 * (a : ℝ) - 4 * ((a + J + 5 : ℕ) : ℝ)) +
        (-b ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * b) := by ring
    _ ≤ (-2 * (a : ℝ) - 4 * ((a + J + 5 : ℕ) : ℝ)) +
        (6 * (j : ℝ) - 2 * w + 10) := add_le_add (le_refl _) hq'
    _ = _ := by linarith only [he]

end SRWTightness
