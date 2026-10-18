import SRWTightness.SourcePairGaussianEndpointInternal
import SRWTightness.FiniteGaussianPathReconstruction

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual compensated source vector is realized by a continuous Brownian prefix
and an independent two-dimensional Gaussian residual, with the original geometry. -/
theorem source_pair_brownian_process_representation
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
    let T := sourceObservationTime t A I
    let n := I - i + 1
    let ν := (gaussianCoordinateLaw (brownianTimeMatrix T n)).prod (independentBridgeLaw ℕ)
    let R := pairResidualMatrix (V false false) (V true true) (V false true) (T n)
    let B := fun p : (Fin n → ℝ) × (ℕ → GaussianCoefficientSpace) ↦
      finiteGaussianBridgedPath T n n p.1 p.2
    IsGaussianProcess (fun v p ↦ B p v) ν ∧
    (∀ v, 0 ≤ v → v ≤ T n → (∫ p, B p v ∂ν) = 0) ∧
    (∀ s r, 0 ≤ s → s ≤ T n → 0 ≤ r → r ≤ T n →
      covariance (fun p ↦ B p s) (fun p ↦ B p r) ν = min s r) ∧
    (∀ᵐ p ∂ν, Continuous (B p)) ∧
    IndepFun (fun p : ((Fin n → ℝ) × (ℕ → GaussianCoefficientSpace)) × (Fin 2 → ℝ) ↦
      B p.1) Prod.snd (ν.prod (gaussianCoordinateLaw R)) ∧
    gaussianCoordinateLaw
      (pairObservationCovarianceMatrix (fun j : Fin n ↦ T (j.val + 1)) (fun _ ↦ 0) V) =
      (ν.prod (gaussianCoordinateLaw R)).map
        (fun p j ↦ match j with
          | Sum.inl a => B p.1 (T (a.val + 1))
          | Sum.inr c => B p.1 (T n) + p.2 (if c then 1 else 0)) := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  have hgap : ∀ j < I - i + 1,
      sourceObservationTime t A I j < sourceObservationTime t A I (j + 1) := by
    intro j hj
    linarith [hg j (by omega)]
  have hR := source_pair_node_residual_posDef b t A hA ht (by linarith) I hI i hi
    z y hz hρ hlo hhi u hu k hk
  dsimp only
  refine ⟨finiteGaussianBridgedPath_gaussian _ _ hgap, ?_, ?_,
    finiteGaussianBridgedPath_ae_continuous _ _,
    finiteGaussianBridgedPath_independent _ _ _, ?_⟩
  · intro v hv hv'
    exact finiteGaussianBridgedPath_mean _ _ (by omega) hgap v
      (by simpa only [sourceObservationTime_zero] using hv) hv'
  · intro s r hs hs' hr hr'
    exact finiteGaussianBridgedPath_covariance _ _ (by omega)
      (sourceObservationTime_zero t A I) hgap s r hs hs' hr hr'
  · apply finiteGaussianBridgedPath_pair_law _ _ (Fin.last (I - i)) (by simp)
      (sourceObservationTime_zero t A I) hgap
    · exact covariance_comm _ _
    · simpa only [Bool.false_eq_true, ↓reduceIte] using hR

end SRWTightness
