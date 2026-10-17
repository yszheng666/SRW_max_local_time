import SRWTightness.SRWHeatKernelMaximum
import SRWTightness.CentralBinomialBounds

namespace SRWTightness

theorem transitionProbability_return_error (n : ℕ) :
    |(n : ℝ) * transitionProbability (2 * n) 0 - 1 / Real.pi| ≤
      1 / (Real.pi * (2 * n + 1)) := by
  simpa only [transitionProbability_return_even] using nat_mul_centralBinomialRatio_sq_error n

theorem transitionProbability_return_le (n : ℕ) (hn : 0 < n) :
    transitionProbability (2 * n) 0 ≤ 1 / (Real.pi * n) := by
  have h := nat_mul_centralBinomialRatio_sq_le n
  rw [transitionProbability_return_even]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ (mul_pos Real.pi_pos hn')).2
  have h' := (le_div_iff₀ Real.pi_pos).mp h
  nlinarith

theorem transitionProbability_uniform_le (n : ℕ) (hn : 2 ≤ n) (z : Site) :
    transitionProbability n z ≤ 1 / (Real.pi * (n / 2 : ℕ)) := by
  calc
    _ ≤ transitionProbability (2 * (n / 2)) 0 :=
      transitionProbability_le_return_even (n / 2) n (by omega) z
    _ ≤ _ := transitionProbability_return_le (n / 2) (by omega)

end SRWTightness
