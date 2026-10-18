import SRWTightness.SourceCommonPairCoarseReferenceSum

open Filter
open scoped Topology
namespace SRWTightness

/-- The early gap depends logarithmically on the distance index, as in equation 8.8. -/
noncomputable def sourceEarlyDistanceGap (a J₀ : ℕ) : ℕ :=
  ⌈20 * Real.log ((a : ℝ) + 2)⌉₊ + J₀

/-- A fixed distance threshold makes the early logarithmic gap at most half the index. -/
theorem source_early_distance_gap_small (J₀ : ℕ) :
    ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ a ≥ a₀, 2 * sourceEarlyDistanceGap a J₀ ≤ a := by
  have hlim : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((tendsto_order.1 hlim).2 (1 / 80 : ℝ) (by norm_num))
  let a₀ : ℕ := ⌈max T (4 * (J₀ : ℝ) + 8)⌉₊
  have hbase := Nat.le_ceil (max T (4 * (J₀ : ℝ) + 8))
  have hpos : 1 ≤ a₀ := by
    have h : (1 : ℝ) ≤ (a₀ : ℝ) := by
      dsimp only [a₀]
      linarith [le_max_right T (4 * (J₀ : ℝ) + 8), show (0 : ℝ) ≤ (J₀ : ℝ) from Nat.cast_nonneg _]
    exact_mod_cast h
  refine ⟨a₀, hpos, ?_⟩
  intro a ha
  have hac : (a₀ : ℝ) ≤ a := Nat.cast_le.mpr ha
  have haT : T ≤ (a : ℝ) + 2 := by
    dsimp only [a₀] at hac
    linarith [le_max_left T (4 * (J₀ : ℝ) + 8)]
  have hlog := (div_lt_iff₀ (by positivity : 0 < (a : ℝ) + 2)).mp (hT _ haT)
  have hc := Nat.ceil_lt_add_one
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20)
      (Real.log_nonneg (by have hn : (0 : ℝ) ≤ a := Nat.cast_nonneg _; linarith : 1 ≤ (a : ℝ) + 2)))
  have hreal : 2 * (sourceEarlyDistanceGap a J₀ : ℝ) ≤ a := by
    simp only [sourceEarlyDistanceGap, Nat.cast_add]
    dsimp only [a₀] at hac
    linarith [le_max_right T (4 * (J₀ : ℝ) + 8)]
  exact_mod_cast hreal

/-- The later gap is small enough compared with the lower coarse cutoff. -/
theorem source_common_gap_cutoff_margin :
    ∀ᶠ t : ℝ in atTop, 3 * sourceCommonPairGap t + 10 ≤ sourceCoarseLowerLevel t := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with t hl ht
  have hg := (sourceCommonPairGap_bounds t ht).2
  have hp := Real.rpow_le_rpow_of_exponent_le
    (by linarith : 1 ≤ 1000 * Real.log t) (by norm_num : (1 : ℝ) ≤ 5 / 2)
  rw [Real.rpow_one] at hp
  have hc := Nat.le_ceil ((1000 * Real.log t) ^ (5 / 2 : ℝ))
  have hreal : 3 * (sourceCommonPairGap t : ℝ) + 10 ≤ (sourceCoarseLowerLevel t : ℝ) := by
    change 3 * (sourceCommonPairGap t : ℝ) + 10 ≤
      (⌈(1000 * Real.log t) ^ (5 / 2 : ℝ)⌉₊ : ℝ)
    linarith
  exact_mod_cast hreal

/-- The actual logarithmic early levels satisfy the manuscript positive-prefix and continuation range. -/
theorem source_early_distance_levels (J₀ : ℕ) :
    ∃ a₀ : ℕ, ∀ᶠ t : ℝ in atTop, ∀ a : ℕ, a₀ ≤ a →
      a < sourceCoarseLowerLevel t + sourceCommonPairGap t →
      0 < a - sourceEarlyDistanceGap a J₀ ∧
      (a : ℝ) / 2 ≤ ((a - sourceEarlyDistanceGap a J₀ : ℕ) : ℝ) ∧
      a + sourceEarlyDistanceGap a J₀ + 5 ≤ 2 * sourceCoarseLowerLevel t := by
  obtain ⟨a₀, ha₀, hh⟩ := source_early_distance_gap_small J₀
  refine ⟨a₀, ?_⟩
  filter_upwards [source_common_gap_cutoff_margin] with t ht
  intro a ha hrange
  have hg := hh a ha
  refine ⟨by omega, ?_, by omega⟩
  rw [Nat.cast_sub (by omega : sourceEarlyDistanceGap a J₀ ≤ a)]
  have hgr : 2 * (sourceEarlyDistanceGap a J₀ : ℝ) ≤ a := by exact_mod_cast hg
  linarith

end SRWTightness
