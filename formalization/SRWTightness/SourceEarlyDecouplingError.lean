import SRWTightness.SourceEarlyReturnError
import SRWTightness.SourceEarlyGapWeight

open Filter
namespace SRWTightness

/-- Equation 8.10 for the actual early gap: the distance-weighted long-segment cost is uniformly
bounded, and the entire return/fine-forest remainder vanishes on the source scale. -/
theorem source_early_decoupling_error (D C B W : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C) (J₀ : ℕ) :
    ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ a : ℕ, a₀ ≤ a →
      a < sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let J := sourceEarlyDistanceGap a J₀
      let ν := a + J + 5
      sourceDecouplingExponent D C B W t ν J ≤
        576 * D * ((a : ℝ) + 1) ^ 2 * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
          sourceDecouplingSmallError C B W t ∧
      576 * D * ((a : ℝ) + 1) ^ 2 * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
          sourceDecouplingSmallError C B W t ≤ 576 * D + sourceDecouplingSmallError C B W t := by
  obtain ⟨a₀, ha₀, hgap⟩ := source_early_distance_gap_small J₀
  obtain ⟨a₁, hlevels⟩ := source_early_distance_levels J₀
  refine ⟨max a₀ a₁, ha₀.trans (le_max_left _ _), ?_⟩
  filter_upwards [source_early_return_error, hlevels] with t hreturn hlevels
  intro a ha hrange
  dsimp only
  let J := sourceEarlyDistanceGap a J₀
  let ν := a + J + 5
  have hJ : J ≤ a := by have hh := hgap a ((le_max_left _ _).trans ha); omega
  have hν := (hlevels a ((le_max_right _ _).trans ha) hrange).2.2
  have hret := hreturn ν hν C hC
  have hJr : (J : ℝ) ≤ a := Nat.cast_le.mpr hJ
  have hn : (ν : ℝ) + 1 ≤ 6 * ((a : ℝ) + 1) := by
    dsimp [ν]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    linarith [show (0 : ℝ) ≤ a from Nat.cast_nonneg _]
  have hsq : ((ν : ℝ) + 1) ^ 2 ≤ 36 * ((a : ℝ) + 1) ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (ν : ℝ) + 1) hn 2
    nlinarith only [hh]
  have hlead := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 16))
    (show 0 ≤ D * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) by positivity)
  constructor
  · change sourceDecouplingExponent D C B W t ν J ≤ _
    unfold sourceDecouplingExponent sourceDecouplingSmallError
    nlinarith only [hlead, hret]
  · have hw := mul_le_mul_of_nonneg_left (source_early_gap_weight a J₀ hJ)
      (show 0 ≤ 576 * D by positivity)
    nlinarith only [hw]

/-- The exact exponent in the source joint-root comparison is uniformly bounded throughout the
actual early-distance range. -/
theorem source_early_decoupling_exponent_bounded (D C B W : ℝ)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (J₀ : ℕ) :
    ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ a : ℕ, a₀ ≤ a →
      a < sourceCoarseLowerLevel t + sourceCommonPairGap t →
      sourceDecouplingExponent D C B W t
        (a + sourceEarlyDistanceGap a J₀ + 5) (sourceEarlyDistanceGap a J₀) ≤ 576 * D + 1 := by
  obtain ⟨a₀, ha₀, hb⟩ := source_early_decoupling_error D C B W hD hC J₀
  refine ⟨a₀, ha₀, ?_⟩
  have he := (tendsto_order.1 (source_decoupling_small_error_tendsto_zero C B W)).2
    (1 : ℝ) (by norm_num)
  filter_upwards [hb, he] with t ht he
  intro a ha hrange
  exact ((ht a ha hrange).1.trans (ht a ha hrange).2).trans (by linarith)

end SRWTightness
