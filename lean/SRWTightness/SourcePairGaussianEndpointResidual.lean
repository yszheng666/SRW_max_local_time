import SRWTightness.ExternalGaussianEndpointResidual
import SRWTightness.SourcePairCompensatedLower

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual compensated pair Gaussian law is an independent endpoint-residual construction. -/
theorem source_pair_gaussian_endpoint_residual
    (hGaussian : GaussianEndpointResidualInput) (b : Site) (t A : ℝ)
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
  have hB := source_pair_brownian_lower t A hA ht I hI i
  have hR := source_pair_node_residual_posDef b t A hA ht (by linarith) I hI i hi
    z y hz hρ hlo hhi u hu k hk
  dsimp only
  let V := fun c d : Bool ↦ covariance
    (normalizedMarkSum _ k (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi) u
      (if c then y else z))
    (normalizedMarkSum _ k (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi) u
      (if d then y else z))
    (markProductLaw (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
      (sourceReferenceIntensity (sourceLowerRadius t) 14) k)
  have hsym : V true false = V false true := covariance_comm _ _
  have hquad (x : Fin (I - i + 1) → ℝ) :
      0 ≤ ∑ j, ∑ l, x j * min (sourceObservationTime t A I (j.val + 1))
        (sourceObservationTime t A I (l.val + 1)) * x l :=
    (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) * ∑ j, x j ^ 2).trans (hB.2 x)
  have hR' : (pairResidualMatrix (V false false) (V true true) (V false true)
      (sourceObservationTime t A I ((Fin.last (I - i)).val + 1))).PosDef := by
    simpa only [V, Fin.val_last, Bool.false_eq_true, ↓reduceIte] using hR
  have hh := hGaussian (I - i + 1) (Fin.last (I - i))
    (fun j ↦ sourceObservationTime t A I (j.val + 1)) V hB.1 hsym hquad hR'
  convert hh using 1
  congr 1
  funext p j
  cases j <;> rfl

end SRWTightness
