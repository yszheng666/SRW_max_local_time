import SRWTightness.SourceEarlyDistanceLevels
import SRWTightness.SourceCommonPairEndpointRatio

open Filter
open scoped Topology
namespace SRWTightness

/-- Every fixed multiple of the logarithmic early gap is eventually below the distance index. -/
theorem source_early_gap_linear_bound (J₀ : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ a₀ : ℕ, ∀ a ≥ a₀, B * ((sourceEarlyDistanceGap a J₀ : ℝ) + 1) ≤ a := by
  have hlim : Tendsto (fun x : ℝ ↦ (20 * B) * (Real.log x / x)) atTop (𝓝 0) := by
    have hh : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using hh.const_mul (20 * B)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((tendsto_order.1 hlim).2 (1 / 4 : ℝ) (by norm_num))
  let a₀ : ℕ := ⌈max T (4 * B * ((J₀ : ℝ) + 2) + 4)⌉₊
  refine ⟨a₀, ?_⟩
  intro a ha
  have hbase := Nat.le_ceil (max T (4 * B * ((J₀ : ℝ) + 2) + 4))
  have hac : (a₀ : ℝ) ≤ a := Nat.cast_le.mpr ha
  have haT : T ≤ (a : ℝ) + 2 := by
    dsimp only [a₀] at hac
    linarith [le_max_left T (4 * B * ((J₀ : ℝ) + 2) + 4)]
  have hlog : (20 * B) * Real.log ((a : ℝ) + 2) < ((a : ℝ) + 2) / 4 := by
    have hh := hT _ haT
    rw [← mul_div_assoc] at hh
    have hh := (div_lt_iff₀ (by positivity : 0 < (a : ℝ) + 2)).mp hh
    linarith
  have hc := Nat.ceil_lt_add_one
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20)
      (Real.log_nonneg (by have hn := Nat.cast_nonneg (α := ℝ) a; linarith :
        1 ≤ (a : ℝ) + 2)))
  have hc' := mul_le_mul_of_nonneg_left hc.le hB
  have hsize : 4 * B * ((J₀ : ℝ) + 2) + 4 ≤ a := by
    dsimp only [a₀] at hac
    linarith [le_max_right T (4 * B * ((J₀ : ℝ) + 2) + 4)]
  simp only [sourceEarlyDistanceGap, Nat.cast_add]
  nlinarith [Nat.cast_nonneg (α := ℝ) a]

/-- The source early barrier automatically makes the reciprocal-barrier tilt admissible. -/
theorem source_early_barrier_tilt (J₀ : ℕ) (C γ : ℝ) (hC : 0 ≤ C) (hγ : γ ≤ 1) :
    ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ a ≥ a₀,
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ γ
      4 ≤ b ∧ b ≤ 4 * ((j : ℝ) + 1) ∧
      0 ≤ 2 / b ∧ 2 / b ≤ 1 / 2 ∧ C * ((J : ℝ) + 1) * (2 / b) ≤ 1 / 4 := by
  obtain ⟨ag, hag, hg⟩ := source_early_distance_gap_small J₀
  obtain ⟨ac, hc⟩ := source_early_gap_linear_bound J₀ (32 * C) (by positivity)
  refine ⟨max ag ac, hag.trans (le_max_left _ _), ?_⟩
  filter_upwards [sourceBarrierSlope_eventually_band] with t ht
  intro a ha
  dsimp only
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ γ
  have hg := hg a ((le_max_left _ _).trans ha)
  have hc := hc a ((le_max_right _ _).trans ha)
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hja : (a : ℝ) / 2 ≤ (j : ℝ) := by
    have hgr : 2 * (J : ℝ) ≤ a := by exact_mod_cast hg
    dsimp [j]
    rw [Nat.cast_sub (by omega : J ≤ a)]
    linarith
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp := Real.rpow_le_rpow_of_exponent_le hj1 hγ
  rw [Real.rpow_one] at hp
  have hp0 := Real.rpow_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) γ
  have hlo : 4 + (j : ℝ) / 2 ≤ b := by
    dsimp [b]
    nlinarith [mul_le_mul_of_nonneg_right ht.1 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hhi : b ≤ 4 * ((j : ℝ) + 1) := by
    dsimp [b]
    nlinarith [mul_le_mul_of_nonneg_right ht.2 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hb4 : 4 ≤ b := by linarith
  have hb : 0 < b := by linarith
  refine ⟨hb4, hhi, by positivity, (div_le_iff₀ hb).2 (by linarith), ?_⟩
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hb).2
  change 32 * C * ((J : ℝ) + 1) ≤ a at hc
  nlinarith

end SRWTightness
