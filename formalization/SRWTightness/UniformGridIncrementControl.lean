import SRWTightness.UniformGridApproximation
import Mathlib.Topology.UniformSpace.HeineCantor

open Filter
open scoped Topology
namespace SRWTightness

/-- Consecutive stopped-grid times are at most one mesh width apart. -/
theorem stoppedUniformTimeGrid_succ_dist (a b : ℝ) (N k : ℕ) (hab : a ≤ b) :
    dist (stoppedUniformTimeGrid a b N (k + 1)) (stoppedUniformTimeGrid a b N k) ≤
      (b - a) / N := by
  have hm := stoppedUniformTimeGrid_mono a b N hab (Nat.le_succ k)
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hm)]
  unfold stoppedUniformTimeGrid
  have hi : min (k + 1) N ≤ min k N + 1 := by omega
  have hr : ((min (k + 1) N : ℕ) : ℝ) - (min k N : ℕ) ≤ 1 := by
    have hc : ((min (k + 1) N : ℕ) : ℝ) ≤ (min k N : ℕ) + 1 := by
      exact_mod_cast hi
    linarith
  calc
    a + (b - a) * (min (k + 1) N : ℕ) / N -
        (a + (b - a) * (min k N : ℕ) / N) =
        (b - a) * (((min (k + 1) N : ℕ) : ℝ) - (min k N : ℕ)) / N := by ring
    _ ≤ (b - a) * 1 / N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr hab))
        (Nat.cast_nonneg N)
    _ = (b - a) / N := by rw [mul_one]

/-- Continuity on a compact interval makes every dyadic-grid increment uniformly small. -/
theorem continuous_dyadic_grid_small_increments (f : ℝ → ℝ) (a b ε : ℝ)
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      dist (f (stoppedUniformTimeGrid a b (2 ^ n) (k + 1)))
        (f (stoppedUniformTimeGrid a b (2 ^ n) k)) < ε := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, huδ⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  have hpow : Tendsto (fun n : ℕ ↦ ((2 : ℝ) ^ n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlim : Tendsto (fun n : ℕ ↦ (b - a) / (2 ^ n : ℕ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat, mul_zero] using
      tendsto_const_nhds.mul hpow
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn k
  apply huδ _ (stoppedUniformTimeGrid_mem a b (2 ^ n) (k + 1) hab (by positivity))
    _ (stoppedUniformTimeGrid_mem a b (2 ^ n) k hab (by positivity))
  exact (stoppedUniformTimeGrid_succ_dist a b (2 ^ n) k hab).trans_lt hn

end SRWTightness
