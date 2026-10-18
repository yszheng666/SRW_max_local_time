import SRWTightness.SRWReturnBounds
import Mathlib.NumberTheory.Harmonic.Bounds

open Finset

namespace SRWTightness

theorem sum_transition_return_even (N : ℕ) :
    (∑ k ∈ range (2 * N), transitionProbability k 0) =
      ∑ k ∈ range N, transitionProbability (2 * k) 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 2 by omega, sum_range_add, ih, sum_range_succ]
    simp [sum_range_succ, transitionProbability_return_odd]

theorem transitionProbability_return_lower (n : ℕ) :
    1 / (Real.pi * ((n : ℝ) + 1)) ≤ transitionProbability (2 * n) 0 := by
  rw [transitionProbability_return_even]
  refine le_trans ?_ (centralBinomialRatio_sq_lower n)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Real.pi_pos]

theorem returnPartial_harmonic_lower (N : ℕ) :
    (harmonic N : ℝ) / Real.pi ≤ ∑ k ∈ range N, transitionProbability (2 * k) 0 := by
  unfold harmonic
  push_cast
  rw [sum_div]
  apply sum_le_sum
  intro k hk
  simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv, one_mul, mul_comm Real.pi⁻¹] using transitionProbability_return_lower k

theorem returnPartial_harmonic_upper (N : ℕ) :
    (∑ k ∈ range (N + 1), transitionProbability (2 * k) 0) ≤ 1 + (harmonic N : ℝ) / Real.pi := by
  induction N with
  | zero => simp [sum_range_succ, transitionProbability_return_even, centralBinomialRatio]
  | succ N ih =>
    rw [sum_range_succ, harmonic_succ]
    push_cast
    have h := transitionProbability_return_le (N + 1) (by omega)
    have he : 1 / (Real.pi * ((N + 1 : ℕ) : ℝ)) = (((N + 1 : ℕ) : ℝ)⁻¹) / Real.pi := by
      simp [div_eq_mul_inv, mul_comm]
    rw [he] at h
    push_cast at h
    rw [add_div]
    linarith

theorem returnPartial_log_lower (N : ℕ) :
    Real.log ((N : ℝ) + 1) / Real.pi ≤ ∑ k ∈ range N, transitionProbability (2 * k) 0 := by
  refine le_trans ?_ (returnPartial_harmonic_lower N)
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic N

theorem returnPartial_log_upper (N : ℕ) :
    (∑ k ∈ range (N + 1), transitionProbability (2 * k) 0) ≤
      1 + (1 + Real.log (N : ℝ)) / Real.pi := by
  refine (returnPartial_harmonic_upper N).trans ?_
  exact add_le_add_right (div_le_div_of_nonneg_right (harmonic_le_one_add_log N) Real.pi_pos.le) 1

end SRWTightness
