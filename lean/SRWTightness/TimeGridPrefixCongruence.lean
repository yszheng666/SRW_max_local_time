import SRWTightness.TimeGridInterpolation

namespace SRWTightness

/-- Coordinates after a retained endpoint do not affect the interpolated prefix. -/
theorem timeGridInterpolation_prefix_congr (T x y : ℕ → ℝ) (n k : ℕ)
    (hk : k ≤ n) (hgap : ∀ j < n, T j < T (j + 1))
    (hxy : ∀ j ≤ k, x j = y j) (v : ℝ) (hv : v ≤ T k) :
    timeGridInterpolation T x n v = timeGridInterpolation T y n v := by
  unfold timeGridInterpolation
  rw [hxy 0 (Nat.zero_le _)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  by_cases hjk : j < k
  · rw [hxy j (by omega), hxy (j + 1) (by omega)]
  · have hkj : k ≤ j := Nat.le_of_not_gt hjk
    have hvj : v ≤ T j := hv.trans (timeGridTime_mono T n hgap hkj (by omega))
    rw [timeGridRamp_left _ _ _ (hgap j hjn) hvj]
    simp only [zero_mul]

end SRWTightness
