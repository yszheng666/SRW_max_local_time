import SRWTightness.SourcePairGaussianEndpointResidual
import SRWTightness.GaussianEndpointResidualInternal

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual compensated pair law has the endpoint-residual representation without an input. -/
theorem source_pair_gaussian_endpoint_residual_internal
    (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : 4 * sourcePairResidualError + 3 + sourceEquilibriumTimeError +
      sourceLowerTimeError ≤ Real.log A)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let m := sourceLowerRadius t
    let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity m 14
    let μ := markProductLaw D M α k
    let F := normalizedMarkSum M k α (2 / Real.pi) u
    let V := fun c d : Bool ↦ covariance (F (if c then y else z)) (F (if d then y else z)) μ
    let T := fun j : Fin (I - i + 1) ↦ sourceObservationTime t A I (j.val + 1)
    let last := Fin.last (I - i)
    gaussianCoordinateLaw (pairObservationCovarianceMatrix T (fun _ ↦ 0) V) =
      ((gaussianCoordinateLaw (fun j l ↦ min (T j) (T l))).prod
        (gaussianCoordinateLaw
          (pairResidualMatrix (V false false) (V true true) (V false true) (T last)))).map
        (fun p j ↦ match j with
          | Sum.inl a => p.1 a
          | Sum.inr c => p.1 last + p.2 (if c then 1 else 0)) := by
  exact source_pair_gaussian_endpoint_residual gaussian_endpoint_residual_input_internal
    b t A hA ht hlog I hI i hi z y hz hρ hlo hhi u hu k hk

end SRWTightness
