import SRWTightness.PolynomialStretchedExponential

namespace SRWTightness

/-- A finite curved-barrier sum is bounded by a summable early part and a terminal remainder. -/
theorem barrier_curvature_sum_bound (N k : ℕ) (d c γ : ℝ)
    (hd : 0 ≤ d) (hc : 0 < c) (hγ : 0 < γ) :
    (∑ j ∈ Finset.range (N + 1), ((j : ℝ) + 1) ^ k *
      Real.exp (-c * (min (j : ℝ) ((N : ℝ) + d - j)) ^ γ)) ≤
      (∑' j : ℕ, ((j : ℝ) + 1) ^ k * Real.exp (-c * (j : ℝ) ^ γ)) +
        ((N : ℝ) + 1) ^ (k + 1) * Real.exp (-c * d ^ γ) := by
  have hs := polynomial_stretched_exponential_summable k c γ hc hγ
  have hpoint : ∀ j ∈ Finset.range (N + 1),
      ((j : ℝ) + 1) ^ k * Real.exp (-c * (min (j : ℝ) ((N : ℝ) + d - j)) ^ γ) ≤
        ((j : ℝ) + 1) ^ k * Real.exp (-c * (j : ℝ) ^ γ) +
          ((N : ℝ) + 1) ^ k * Real.exp (-c * d ^ γ) := by
    intro j hj
    have hjN : j ≤ N := by have h := Finset.mem_range.mp hj; omega
    have hjN' : (j : ℝ) ≤ N := by exact_mod_cast hjN
    rcases le_total (j : ℝ) ((N : ℝ) + d - j) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right h]
      have hpow := Real.rpow_le_rpow hd (show d ≤ (N : ℝ) + d - j by linarith) hγ.le
      have hexp : Real.exp (-c * ((N : ℝ) + d - j) ^ γ) ≤
          Real.exp (-c * d ^ γ) := Real.exp_le_exp.mpr (by nlinarith)
      have hpoly : ((j : ℝ) + 1) ^ k ≤ ((N : ℝ) + 1) ^ k :=
        pow_le_pow_left₀ (by positivity) (by linarith) k
      have hb := mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
      exact hb.trans (le_add_of_nonneg_left (by positivity))
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 1),
        (((j : ℝ) + 1) ^ k * Real.exp (-c * (j : ℝ) ^ γ) +
          ((N : ℝ) + 1) ^ k * Real.exp (-c * d ^ γ)) := Finset.sum_le_sum hpoint
    _ = (∑ j ∈ Finset.range (N + 1),
        ((j : ℝ) + 1) ^ k * Real.exp (-c * (j : ℝ) ^ γ)) +
          ((N : ℝ) + 1) ^ (k + 1) * Real.exp (-c * d ^ γ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      rw [pow_succ]
      ring
    _ ≤ _ := add_le_add (hs.sum_le_tsum _ (fun _ _ ↦ by positivity)) le_rfl

end SRWTightness
