import SRWTightness.GeometricTerminalIndex

namespace SRWTightness

theorem geometricTerminalIndex_log_bounds (A q L : ℝ) (hA : 0 < A) (hq : 1 < q)
    (hAL : A ≤ L) :
    0 ≤ Real.log L - Real.log (A * q ^ geometricTerminalIndex A q L hA hq hAL) ∧
      Real.log L - Real.log (A * q ^ geometricTerminalIndex A q L hA hq hAL) ≤ Real.log q := by
  have hq0 : 0 < q := by linarith
  have hL : 0 < L := hA.trans_le hAL
  obtain ⟨hl, hu⟩ := geometricTerminalIndex_spec A q L hA hq hAL
  have hlLog := Real.log_le_log (by positivity) hl
  have huLog := Real.log_le_log hL hu.le
  rw [pow_succ, ← mul_assoc, Real.log_mul (by positivity) hq0.ne'] at huLog
  exact ⟨by linarith, by linarith⟩

theorem geometricTerminalIndex_log_size (A q L : ℝ) (hA : 0 < A) (hq : 1 < q)
    (hAL : A ≤ L) :
    (geometricTerminalIndex A q L hA hq hAL : ℝ) ≤
      (Real.log L - Real.log A) / Real.log q := by
  have hq0 : 0 < q := by linarith
  have hl := (geometricTerminalIndex_spec A q L hA hq hAL).1
  have hh := Real.log_le_log (by positivity) hl
  rw [Real.log_mul hA.ne' (pow_ne_zero _ hq0.ne'), Real.log_pow] at hh
  apply (le_div_iff₀ (Real.log_pos hq)).mpr
  linarith

/-- The last radius in (5.7) leaves exactly six log(t), up to one fixed log-ratio. -/
theorem source_terminal_log_bounds (m t A q : ℝ) (hm : 0 < m) (ht : 0 < t)
    (hA : 0 < A) (hq : 1 < q) (hcut : A ≤ m / t ^ 6) :
    let I := geometricTerminalIndex A q (m / t ^ 6) hA hq hcut
    0 ≤ Real.log m - Real.log (A * q ^ I) - 6 * Real.log t ∧
      Real.log m - Real.log (A * q ^ I) - 6 * Real.log t ≤ Real.log q := by
  have hh := geometricTerminalIndex_log_bounds A q (m / t ^ 6) hA hq hcut
  have he : Real.log (m / t ^ 6) = Real.log m - 6 * Real.log t := by
    rw [Real.log_div hm.ne' (pow_ne_zero _ ht.ne'), Real.log_pow]
    norm_num
  rw [he] at hh
  dsimp only
  constructor <;> linarith [hh.1, hh.2]

end SRWTightness
