import SRWTightness.GaussianGridPath
import SRWTightness.SourceBridgedPath

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Translating the observations by their comparison means removes the source centering exactly. -/
theorem sourceBridgedPath_gaussian_centering (t A : ℝ) (I : ℕ)
    (x : Fin ((I + 1) + 1) → ℝ) (ω : ℕ → GaussianCoefficientSpace) (v : ℝ) :
    sourceBridgedPath t A I
      (fun i ↦ 2 * sourceObservationTime t A I (i.val + 1) + x i) ω v =
      gaussianGridPath (sourceObservationTime t A I) (I + 1) (x, ω) v := by
  have he : ((fun i : Fin ((I + 1) + 1) ↦
      2 * sourceObservationTime t A I (i.val + 1) + x i) -
      (fun i ↦ 2 * sourceObservationTime t A I (i.val + 1))) = x := by
    funext i
    simp
  unfold sourceBridgedPath sourceAveragePath
  rw [he]
  rfl

/-- The actual source comparison mesh yields a continuous centered Gaussian path with Brownian covariance. -/
theorem sourceGaussianGridPath_properties (t A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A)
    (ht : sourceGaussianThreshold A ≤ t) (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) :
    let T := sourceObservationTime t A I
    let ν := (gaussianCoordinateLaw (brownianTimeMatrix T ((I + 1) + 1))).prod (independentBridgeLaw ℕ)
    let B := gaussianGridPath T (I + 1)
    IsGaussianProcess (fun v p ↦ B p v) ν ∧
      (∀ v : ℝ, 0 ≤ v → v ≤ T (I + 1) → (∫ p, B p v ∂ν) = 0) ∧
      (∀ s r : ℝ, 0 ≤ s → s ≤ T (I + 1) → 0 ≤ r → r ≤ T (I + 1) →
        cov[fun p ↦ B p s, fun p ↦ B p r; ν] = min s r) ∧
      (∀ᵐ p ∂ν, Continuous (B p)) := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  have hg' : ∀ j < I + 1, sourceObservationTime t A I j < sourceObservationTime t A I (j + 1) :=
    fun j hj ↦ by linarith [hg j (by omega)]
  refine ⟨gaussianGridPath_gaussian _ _ hg', ?_, ?_, gaussianGridPath_ae_continuous _ _⟩
  · intro v hv hv'
    exact gaussianGridPath_mean _ _ (by omega) hg' v
      (by simpa only [sourceObservationTime_zero] using hv) hv'
  · intro s r hs hs' hr hr'
    exact gaussianGridPath_covariance _ _ (by omega) (sourceObservationTime_zero t A I)
      hg s r hs hs' hr hr'

end SRWTightness
