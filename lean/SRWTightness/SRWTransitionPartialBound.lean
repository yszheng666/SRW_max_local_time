import SRWTightness.SRWInverseDistanceBound

open Finset

namespace SRWTightness

theorem transitionPartial_distance_le (N : ℕ) (hN : 2 ≤ N) (z : Site) (hz : 0 < normSq z) :
    (∑ k ∈ range N, transitionProbability k z) ≤
      2 + (N : ℝ) * ((8 * Real.exp 1) / (Real.pi * normSq z)) := by
  have hinit : (∑ k ∈ range 2, transitionProbability k z) ≤ 2 := by
    calc
      _ ≤ ∑ _k ∈ range 2, (1 : ℝ) := sum_le_sum (fun k _ ↦ transitionProbability_le_one k z)
      _ = _ := by norm_num
  have htail : (∑ k ∈ range (N - 2), transitionProbability (2 + k) z) ≤
      ((N - 2 : ℕ) : ℝ) * ((8 * Real.exp 1) / (Real.pi * normSq z)) := by
    calc
      _ ≤ ∑ _k ∈ range (N - 2), (8 * Real.exp 1) / (Real.pi * normSq z) :=
        sum_le_sum (fun k _ ↦ transitionProbability_distance_le (2 + k) (by omega) z hz)
      _ = _ := by simp
  have hcast : ((N - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 2
  have htail' := htail.trans (mul_le_mul_of_nonneg_right hcast (by positivity))
  conv_lhs => rw [show N = 2 + (N - 2) by omega, sum_range_add]
  linarith

end SRWTightness
