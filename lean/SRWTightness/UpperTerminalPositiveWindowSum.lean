import SRWTightness.UpperTerminalPolynomialWeight
import SRWTightness.UpperTerminalGaussianWindowSum

namespace SRWTightness

/-- The positive terminal polynomial weights sum at the scale required in source (4.32). -/
theorem upper_terminal_positive_window_sum (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ d S v : ℝ, 1 ≤ d → 0 ≤ S → 0 ≤ v → v ≤ 1 → ∀ M : ℕ,
      (∑ J ∈ Finset.range M,
        (S + ((J : ℝ) + v)) * (1 + ((J : ℝ) + v) / Real.sqrt d) / d *
          Real.exp (-c * ((J : ℝ) + v) ^ 2 / d)) ≤ C * (1 + S / Real.sqrt d) := by
  obtain ⟨C, hC, hsum⟩ := upper_terminal_gaussian_window_sum c hc
  refine ⟨2 * C, by positivity, ?_⟩
  intro d S v hd hS hv hv1 M
  have hd0 : 0 < d := by linarith
  have hpoint (J : ℕ) :
      (S + ((J : ℝ) + v)) * (1 + ((J : ℝ) + v) / Real.sqrt d) / d *
        Real.exp (-c * ((J : ℝ) + v) ^ 2 / d) ≤
      (2 * (1 + S / Real.sqrt d)) * upperTerminalGaussianKernel d c ((J : ℝ) + v) := by
    apply (mul_le_mul_of_nonneg_right
      (upper_terminal_polynomial_weight d S (J + v) hd0 hS (by positivity))
      (Real.exp_nonneg _)).trans_eq
    unfold upperTerminalGaussianKernel
    ring
  have hfactor : 0 ≤ 2 * (1 + S / Real.sqrt d) := by positivity
  calc
    _ ≤ ∑ J ∈ Finset.range M, (2 * (1 + S / Real.sqrt d)) *
        upperTerminalGaussianKernel d c ((J : ℝ) + v) :=
      Finset.sum_le_sum (fun J _ ↦ hpoint J)
    _ = (2 * (1 + S / Real.sqrt d)) *
        ∑ J ∈ Finset.range M, upperTerminalGaussianKernel d c ((J : ℝ) + v) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * (1 + S / Real.sqrt d)) * C :=
      mul_le_mul_of_nonneg_left (hsum d hd v hv hv1 M) hfactor
    _ = _ := by ring

end SRWTightness
