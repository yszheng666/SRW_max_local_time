import SRWTightness.SourceObservationTime
import SRWTightness.TimeGridInterpolation

namespace SRWTightness

/-- The retained actual time grid supplies both hypotheses needed for Brownian-block coercivity. -/
theorem source_pair_brownian_lower (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) :
    (∀ j : Fin (I - i + 1), sourceObservationTime t A I (j.val + 1) ≤
      sourceObservationTime t A I ((Fin.last (I - i)).val + 1)) ∧
    (∀ x : Fin (I - i + 1) → ℝ, (1 / 4 : ℝ) * (∑ j, x j ^ 2) ≤
      ∑ j, ∑ l, x j * min (sourceObservationTime t A I (j.val + 1))
        (sourceObservationTime t A I (l.val + 1)) * x l) := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  constructor
  · intro j
    apply timeGridTime_mono (sourceObservationTime t A I) (I - i + 1)
    · intro a ha
      linarith [hg a (by omega)]
    · simp only [Fin.val_last]
      omega
    · simp only [Fin.val_last]
      omega
  · intro x
    exact brownianTimeMatrix_quadratic_lower (sourceObservationTime t A I)
      (sourceObservationTime_zero t A I) (I - i + 1) 1 (by norm_num)
      (fun a ha ↦ hg a (by omega)) x

end SRWTightness
