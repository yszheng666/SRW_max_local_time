import SRWTightness.ExternalFiniteGaussianBridgeKernel

namespace SRWTightness

/-- Later mesh intervals cannot change interpolation before the retained endpoint. -/
theorem timeGridInterpolation_prefix (T x : ℕ → ℝ) (n M : ℕ) (hn : n ≤ M)
    (hgap : ∀ j < M, T j < T (j + 1)) (v : ℝ) (hv : v ≤ T n) :
    timeGridInterpolation T x M v = timeGridInterpolation T x n v := by
  unfold timeGridInterpolation
  congr 1
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro j hj hjn
  have hjM := Finset.mem_range.mp hj
  have hnj : n ≤ j := by simpa only [Finset.mem_range, not_lt] using hjn
  rw [timeGridRamp_left _ _ _ (hgap j hjM)
    (hv.trans (timeGridTime_mono T M hgap hnj hjM.le)), zero_mul]

/-- All auxiliary bridges after the retained endpoint vanish on the prefix. -/
theorem timeGridBridge_prefix (T : ℕ → ℝ) (n M : ℕ) (hn : n ≤ M)
    (hgap : ∀ j < M, T j < T (j + 1)) (ω : ℕ → GaussianCoefficientSpace)
    (v : ℝ) (hv : v ≤ T n) : timeGridBridge T M ω v = timeGridBridge T n ω v := by
  unfold timeGridBridge
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro j hj hjn
  have hjM := Finset.mem_range.mp hj
  have hnj : n ≤ j := by simpa only [Finset.mem_range, not_lt] using hjn
  exact localizedIntervalBridge_left _ _ _
    (hv.trans (timeGridTime_mono T M hgap hnj hjM.le)) _

theorem finiteGaussianBridgedPath_prefix (T : ℕ → ℝ) (n M : ℕ) (hn : n ≤ M)
    (hgap : ∀ j < M, T j < T (j + 1)) (x : Fin n → ℝ)
    (ω : ℕ → GaussianCoefficientSpace) (v : ℝ) (hv : v ≤ T n) :
    finiteGaussianBridgedPath T n M x ω v = finiteGaussianBridgedPath T n n x ω v := by
  unfold finiteGaussianBridgedPath
  rw [timeGridInterpolation_prefix T _ n M hn hgap v hv,
    timeGridBridge_prefix T n M hn hgap ω v hv]

end SRWTightness
