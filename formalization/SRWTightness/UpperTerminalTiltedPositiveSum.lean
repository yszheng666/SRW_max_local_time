import SRWTightness.UpperTerminalPositiveWindowSum

namespace SRWTightness

/-- Tilted, rounded positive windows obey the same scale with an explicit exponential cost. -/
theorem upper_terminal_tilted_positive_sum (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ d S β v : ℝ, 1 ≤ d → 0 ≤ S → 0 ≤ v → v ≤ 1 → ∀ M : ℕ,
      (∑ J ∈ Finset.range M,
        (S + ((J : ℝ) + v)) * (1 + ((J : ℝ) + v) / Real.sqrt d) / d *
          Real.exp (β * ((J : ℝ) + v) - c * (max ((J : ℝ) + v - 1) 0) ^ 2 / d)) ≤
        Real.exp (c / d + 2 * d * β ^ 2 / c) * C * (1 + S / Real.sqrt d) := by
  obtain ⟨C, hC, hsum⟩ := upper_terminal_positive_window_sum (3 * c / 8) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro d S β v hd hS hv hv1 M
  have hd0 : 0 < d := by linarith
  let E := Real.exp (c / d + 2 * d * β ^ 2 / c)
  have hpoint (J : ℕ) :
      (S + ((J : ℝ) + v)) * (1 + ((J : ℝ) + v) / Real.sqrt d) / d *
          Real.exp (β * ((J : ℝ) + v) - c * (max ((J : ℝ) + v - 1) 0) ^ 2 / d) ≤
      E * ((S + ((J : ℝ) + v)) * (1 + ((J : ℝ) + v) / Real.sqrt d) / d *
        Real.exp (-(3 * c / 8) * ((J : ℝ) + v) ^ 2 / d)) := by
    have hq : 0 ≤ (J : ℝ) + v := by positivity
    have he : Real.exp (β * ((J : ℝ) + v) - c * (max ((J : ℝ) + v - 1) 0) ^ 2 / d) ≤
        E * Real.exp (-(3 * c / 8) * ((J : ℝ) + v) ^ 2 / d) := by
      dsimp [E]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      convert upper_terminal_positive_rounded_tilt d c β (J + v) hd0 hc hq using 1
        <;> first | rfl | ring
    apply (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq
    ring
  calc
    _ ≤ ∑ J ∈ Finset.range M, E *
        ((S + ((J : ℝ) + v)) * (1 + ((J : ℝ) + v) / Real.sqrt d) / d *
          Real.exp (-(3 * c / 8) * ((J : ℝ) + v) ^ 2 / d)) :=
      Finset.sum_le_sum (fun J _ ↦ hpoint J)
    _ = E * ∑ J ∈ Finset.range M,
        (S + ((J : ℝ) + v)) * (1 + ((J : ℝ) + v) / Real.sqrt d) / d *
          Real.exp (-(3 * c / 8) * ((J : ℝ) + v) ^ 2 / d) := by rw [Finset.mul_sum]
    _ ≤ E * (C * (1 + S / Real.sqrt d)) :=
      mul_le_mul_of_nonneg_left (hsum d S v hd hS hv hv1 M) (Real.exp_nonneg _)
    _ = _ := by ring

end SRWTightness
