import SRWTightness.SourceObservationTime

namespace SRWTightness

/-- Reversing the actual average-time mesh separates consecutive spatial deficits by at least one. -/
theorem source_pair_shell_deficit_gap (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i < I) :
    1 ≤ (sourceLowerTime (sourceLowerRadius t) -
      sourceObservationTime t A I (I - (i + 1) + 1)) -
      (sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)) := by
  have h := sourceObservationTime_gaps t A hA ht I hI (I - i) (by omega)
  have he : I - (i + 1) + 1 = I - i := by omega
  rw [he]
  linarith

end SRWTightness
