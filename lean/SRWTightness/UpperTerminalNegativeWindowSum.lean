import SRWTightness.UpperTerminalRoundedTilt

namespace SRWTightness

/-- Negative terminal windows have no positive quadratic penalty and a bounded tilt cost. -/
theorem upper_terminal_negative_window (d S β q Q c : ℝ)
    (hd : 0 < d) (hQ : 0 ≤ Q) (hQS : Q ≤ S) (hq : -Q ≤ q) (hq0 : q ≤ 0) :
    (S + q) * (1 + max q 0 / Real.sqrt d) / d *
        Real.exp (β * q - c * (max (q - 1) 0) ^ 2 / d) ≤
      S / d * Real.exp (|β| * Q) := by
  rw [max_eq_right hq0, max_eq_right (by linarith : q - 1 ≤ 0)]
  norm_num only [zero_div, add_zero, mul_one]
  simp only [mul_zero, zero_div, sub_zero]
  have hm := mul_le_mul_of_nonneg_right (neg_le_abs β) (by linarith : 0 ≤ -q)
  have hn := mul_le_mul_of_nonneg_left (show -q ≤ Q by linarith) (abs_nonneg β)
  have he : β * q ≤ |β| * Q := by nlinarith
  have hpoly : (S + q) / d ≤ S / d :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  exact mul_le_mul hpoly (Real.exp_le_exp.mpr he) (Real.exp_nonneg _)
    (div_nonneg (by linarith) hd.le)

/-- Summing a finite negative range costs only its cardinality and the endpoint tilt. -/
theorem upper_terminal_negative_window_sum (I : Finset ℕ) (q : ℕ → ℝ) (d S β Q c : ℝ)
    (hd : 0 < d) (hQ : 0 ≤ Q) (hQS : Q ≤ S)
    (hq : ∀ J ∈ I, -Q ≤ q J ∧ q J ≤ 0) :
    (∑ J ∈ I, (S + q J) * (1 + max (q J) 0 / Real.sqrt d) / d *
      Real.exp (β * q J - c * (max (q J - 1) 0) ^ 2 / d)) ≤
        (I.card : ℝ) * (S / d * Real.exp (|β| * Q)) := by
  calc
    _ ≤ ∑ J ∈ I, S / d * Real.exp (|β| * Q) :=
      Finset.sum_le_sum (fun J hJ ↦
        upper_terminal_negative_window d S β (q J) Q c hd hQ hQS (hq J hJ).1 (hq J hJ).2)
    _ = _ := by simp

end SRWTightness
