import SRWTightness.SourceUpperLiteralIntegerKernel
import SRWTightness.SourceUpperIntegerWindowInfiniteBound

namespace SRWTightness

/-- The exact integer sum in manuscript (4.29), with its original S(q) coefficient. -/
noncomputable def sourceUpperLiteralIntegerSeries (t s c L : ℝ) : ℝ :=
  let Q := 7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)
  ∑' n : ℕ, sourceUpperLiteralIntegerKernel t s c L (⌈-Q⌉ + n)

/-- Restoring the original S(q) preserves convergence and costs only a fixed factor. -/
theorem source_upper_literal_integer_series_bounds (t s c L : ℝ)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t))
    (hr : 3 ≤ upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ))
    (hs : Summable (fun n : ℕ ↦ sourceUpperIntegerWindowKernel t s c L
      (⌈-(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ))⌉ + n))) :
    Summable (fun n : ℕ ↦ sourceUpperLiteralIntegerKernel t s c L
      (⌈-(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ))⌉ + n)) ∧
      sourceUpperIntegerWindowSeries t s c L ≤ 4 * sourceUpperLiteralIntegerSeries t s c L := by
  let a : ℤ := ⌈-(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ))⌉
  have hb (n : ℕ) := source_upper_literal_integer_kernel_bounds t s c L (a + n) hd hr (by
    have ha := Int.le_ceil (-(7 + s +
      upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)))
    simp only [Int.cast_add, Int.cast_natCast]
    dsimp [a]
    linarith [Nat.cast_nonneg (α := ℝ) n])
  have hnew : Summable (fun n : ℕ ↦ sourceUpperLiteralIntegerKernel t s c L (a + n)) :=
    Summable.of_nonneg_of_le (fun n ↦ (hb n).1) (fun n ↦ (hb n).2.1) hs
  refine ⟨hnew, ?_⟩
  have hh := hs.tsum_le_tsum (fun n ↦ (hb n).2.2) (hnew.mul_left 4)
  rw [tsum_mul_left] at hh
  exact hh

/-- The literal integer series is nonnegative at the eventual admissible manuscript depths. -/
theorem source_upper_literal_integer_series_nonneg (t s c L : ℝ)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t))
    (hr : 3 ≤ upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) :
    0 ≤ sourceUpperLiteralIntegerSeries t s c L := by
  unfold sourceUpperLiteralIntegerSeries
  apply tsum_nonneg
  intro n
  apply (source_upper_literal_integer_kernel_bounds t s c L _ hd hr ?_).1
  have ha := Int.le_ceil (-(7 + s +
    upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)))
  simp only [Int.cast_add, Int.cast_natCast]
  linarith [Nat.cast_nonneg (α := ℝ) n]

end SRWTightness
