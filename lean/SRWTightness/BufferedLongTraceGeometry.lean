import SRWTightness.BufferedLongEscapeParameter

namespace SRWTightness

/-- Buffered long and retained-trace radii have exponential separation and trace error. -/
theorem buffered_long_trace_geometry (ρ H J : ℝ) (hρ : 2 ≤ ρ)
    (hH : 0 ≤ H) (hHρ : H ≤ ρ) (hJ : 1 ≤ J) :
    let a := Real.exp 1 * ρ + H + 2
    let B := Real.exp (J + 1) * ρ + H
    0 < a ∧ 0 < B ∧ Real.exp (J - 1) * a ≤ B ∧
      (a / B) * (1 + Real.log (B / a)) ≤
        (2 * Real.exp 1) * (J + 1) * Real.exp (-J) := by
  dsimp only
  let a := Real.exp 1 * ρ + H + 2
  let B := Real.exp (J + 1) * ρ + H
  have hρ0 : 0 < ρ := by linarith
  have he := Real.exp_one_gt_two
  have he0 := Real.exp_pos 1
  have hE := Real.exp_pos (J + 1)
  have hE1 : 1 ≤ Real.exp (J + 1) := Real.one_le_exp_iff.mpr (by linarith)
  have ha : 0 < a := by dsimp [a]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have har : ρ ≤ a := by dsimp [a]; nlinarith
  have he2 : Real.exp 1 + 2 ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have ha2 : a ≤ Real.exp 2 * ρ := by
    have := mul_le_mul_of_nonneg_right he2 hρ0.le
    dsimp [a]; nlinarith
  have hBlo : Real.exp (J + 1) * ρ ≤ B := by dsimp [B]; linarith
  have hBhi : B ≤ Real.exp (J + 2) * ρ := by
    rw [show J + 2 = 1 + (J + 1) by ring, Real.exp_add 1 (J + 1)]
    have := mul_le_mul_of_nonneg_right hE1 hρ0.le
    dsimp [B]; nlinarith [mul_nonneg (by linarith : 0 ≤ Real.exp 1 - 2)
      (mul_nonneg hE.le hρ0.le)]
  have hsep : Real.exp (J - 1) * a ≤ B := by
    calc
      _ ≤ Real.exp (J - 1) * (Real.exp 2 * ρ) :=
        mul_le_mul_of_nonneg_left ha2 (Real.exp_pos _).le
      _ = Real.exp (J + 1) * ρ := by
        rw [← mul_assoc, ← Real.exp_add]; congr 2 <;> ring
      _ ≤ B := hBlo
  have hab : a / B ≤ Real.exp (1 - J) := by
    apply (div_le_iff₀ hB).mpr
    have hh := mul_le_mul_of_nonneg_left hsep (Real.exp_pos (1 - J)).le
    simpa only [← mul_assoc, ← Real.exp_add, show 1 - J + (J - 1) = 0 by ring,
      Real.exp_zero, one_mul] using hh
  have hlog : Real.log (B / a) ≤ J + 2 := by
    have hh : B / a ≤ Real.exp (J + 2) := by
      apply (div_le_iff₀ ha).mpr
      exact hBhi.trans (mul_le_mul_of_nonneg_left har (Real.exp_pos _).le)
    simpa only [Real.log_exp] using Real.log_le_log (div_pos hB ha) hh
  refine ⟨ha, hB, hsep, ?_⟩
  calc
    (a / B) * (1 + Real.log (B / a)) ≤ (a / B) * (J + 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg ha.le hB.le)
    _ ≤ Real.exp (1 - J) * (J + 3) :=
      mul_le_mul_of_nonneg_right hab (by linarith)
    _ ≤ Real.exp (1 - J) * (2 * (J + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = (2 * Real.exp 1) * (J + 1) * Real.exp (-J) := by
      rw [show 1 - J = 1 + (-J) by ring, Real.exp_add 1 (-J)]; ring

end SRWTightness
