import SRWTightness.PotentialKernelRemainder
import SRWTightness.SRWReturnPartial
import SRWTightness.SRWTransitionPartialBound

open Finset

namespace SRWTightness

theorem potentialKernel_log_upper_finite (z : Site) (N : ℕ) (hN : 0 < N) :
    potentialKernel z ≤ Real.log (N : ℝ) / Real.pi + 1 + 1 / Real.pi + Real.pi * normSq z / N := by
  have hr := potentialKernel_even_remainder_le z N hN
  rw [sum_sub_distrib, sum_transition_return_even] at hr
  have hp : 0 ≤ ∑ k ∈ range (2 * N), transitionProbability k z :=
    sum_nonneg (fun k _ ↦ transitionProbability_nonneg k z)
  have hs : (∑ k ∈ range N, transitionProbability (2 * k) 0) ≤
      ∑ k ∈ range (N + 1), transitionProbability (2 * k) 0 := by
    rw [sum_range_succ]
    linarith [transitionProbability_nonneg (2 * N) 0]
  have hb := hs.trans (returnPartial_log_upper N)
  rw [add_div] at hb
  linarith

theorem potentialKernel_log_lower_finite (z : Site) (hz : 0 < normSq z) (N : ℕ) (hN : 0 < N) :
    Real.log ((N : ℝ) + 1) / Real.pi - 2 -
      (2 * N : ℕ) * ((8 * Real.exp 1) / (Real.pi * normSq z)) ≤ potentialKernel z := by
  have hr := (potentialKernel_even_remainder_bounds z N).1
  rw [sum_sub_distrib, sum_transition_return_even] at hr
  have hp := transitionPartial_distance_le (2 * N) (by omega) z hz
  have hs := returnPartial_log_lower N
  linarith

end SRWTightness
