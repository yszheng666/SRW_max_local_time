import SRWTightness.SourceObservationTime
import SRWTightness.ObservationMeshInterpolation

namespace SRWTightness

/-- The actual centered average interpolation, stopping at v_0 before the site coordinate. -/
noncomputable def sourceAveragePath (t A : ℝ) (I : ℕ)
    (x : Fin ((I + 1) + 1) → ℝ) : C(ℝ, ℝ) :=
  orderedObservationPath (sourceObservationTime t A I)
    (x - fun i ↦ 2 * sourceObservationTime t A I (i.val + 1))

theorem sourceAveragePath_node (t A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A)
    (ht : sourceGaussianThreshold A ≤ t) (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (x : Fin ((I + 1) + 1) → ℝ) (i : Fin (I + 1)) :
    sourceAveragePath t A I x (sourceObservationTime t A I (i.val + 1)) =
      x i.castSucc - 2 * sourceObservationTime t A I (i.val + 1) := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  exact orderedObservationPath_node _
    (fun j hj ↦ by linarith [hg j (by omega)]) _ i

theorem sourceAveragePath_zero (t A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A)
    (ht : sourceGaussianThreshold A ≤ t) (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (x : Fin ((I + 1) + 1) → ℝ) : sourceAveragePath t A I x 0 = 0 := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  have hh := orderedObservationPath_zero (sourceObservationTime t A I)
    (fun j hj ↦ by linarith [hg j (by omega)])
    (x - fun i ↦ 2 * sourceObservationTime t A I (i.val + 1))
  simpa only [sourceAveragePath, sourceObservationTime_zero] using hh

/-- The complete average path is centered by subtracting exactly 2v on the source interval. -/
theorem sourceAveragePath_centered (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (x : Fin ((I + 1) + 1) → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hv' : v ≤ sourceEquilibriumTime b (sourceLowerRadius t) A 14) :
    sourceAveragePath t A I x v =
      orderedObservationPath (sourceObservationTime t A I) x v - 2 * v := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  exact orderedObservationPath_centered _ (sourceObservationTime_zero t A I) (by omega)
    (fun j hj ↦ by linarith [hg j (by omega)]) x 2 v
    (by simpa using hv)
    (by simpa only [sourceObservationTime_last_average b] using hv')

/-- A continuous bridge perturbation vanishing at the observations preserves the discrete barrier. -/
theorem sourceAveragePath_barrier_at_node (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (x : Fin ((I + 1) + 1) → ℝ) (p : C(ℝ, ℝ)) (q d γ : ℝ)
    (hp : ∀ i : Fin (I + 1), p (sourceObservationTime t A I (i.val + 1)) = 0)
    (hbar : ∀ v : ℝ, 0 ≤ v → v ≤ sourceEquilibriumTime b (sourceLowerRadius t) A 14 →
      sourceAveragePath t A I x v + p v ≤ q - (d - v) ^ γ) (i : Fin (I + 1)) :
    x i.castSucc ≤ 2 * sourceObservationTime t A I (i.val + 1) +
      q - (d - sourceObservationTime t A I (i.val + 1)) ^ γ := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  have hs : ∀ j < I + 1, sourceObservationTime t A I j <
      sourceObservationTime t A I (j + 1) := fun j hj ↦ by linarith [hg j (by omega)]
  have hlo := timeGridTime_mono (sourceObservationTime t A I) (I + 1) hs
    (show 0 ≤ i.val + 1 by omega) (show i.val + 1 ≤ I + 1 by omega)
  have hup := timeGridTime_mono (sourceObservationTime t A I) (I + 1) hs
    (show i.val + 1 ≤ I + 1 by omega) le_rfl
  rw [sourceObservationTime_zero] at hlo
  rw [sourceObservationTime_last_average b] at hup
  have hh := hbar _ hlo hup
  rw [sourceAveragePath_node t A hA ht I hI x i, hp i, add_zero] at hh
  linarith

end SRWTightness
