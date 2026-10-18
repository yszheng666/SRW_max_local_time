import SRWTightness.SourceUpperIntegerWindowSupport
import SRWTightness.IntegerRayFiniteSum

namespace SRWTightness

/-- The original infinite integer-window sum, starting at the rounded manuscript cutoff. -/
noncomputable def sourceUpperIntegerWindowSeries (t s c L : ℝ) : ℝ :=
  let Q := 7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)
  ∑' n : ℕ, sourceUpperIntegerWindowKernel t s c L (⌈-Q⌉ + n)

/-- Supported finite chronological windows are dominated by the original convergent integer sum. -/
theorem source_upper_integer_window_infinite_bound (t s κ L : ℝ)
    (ht : 2 ≤ t) (hκ : 0 ≤ κ)
    (hd : 1 ≤ upperTerminalDepth (sourceUpperLogRadius t)) (hL : 0 < L)
    (hsum : Summable (fun n : ℕ ↦ sourceUpperIntegerWindowKernel t s (κ / 4) L
      (⌈-(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ))⌉ + n))) :
    (∑ i ∈ sourceUpperSupportedWindowIndices t s,
      sourceUpperOriginalGaussianWindowKernel t s κ L (t - 1 + (i : ℝ))) ≤
      Real.exp (2 + κ / 2) * sourceUpperIntegerWindowSeries t s (κ / 4) L := by
  classical
  let Q := 7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)
  let a : ℤ := ⌈-Q⌉
  let I := (sourceUpperSupportedWindowIndices t s).image
    (integerDeficitWindowIndex (sourceUpperTarget t s - t + 1))
  have hI (z : ℤ) (hz : z ∈ I) : a ≤ z := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Int.ceil_le.mpr (source_upper_integer_supported_window_cutoff t s i hi)
  have hnonneg (n : ℕ) : 0 ≤ sourceUpperIntegerWindowKernel t s (κ / 4) L (a + n) := by
    apply source_upper_integer_window_kernel_nonneg t s (κ / 4) L _ (by linarith)
    have ha : -Q ≤ (a : ℝ) := Int.le_ceil _
    simp only [Int.cast_add, Int.cast_natCast]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact (source_upper_integer_supported_window_sum t s κ L ht hκ hd hL).trans
    (mul_le_mul_of_nonneg_left
      (integer_ray_finite_sum (sourceUpperIntegerWindowKernel t s (κ / 4) L) a I hI
        hnonneg hsum) (Real.exp_nonneg _))

end SRWTightness
