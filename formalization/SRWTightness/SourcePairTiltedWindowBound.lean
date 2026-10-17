import SRWTightness.SourcePairGaussianWindowBound
import SRWTightness.SourcePairWindowApproximation

open MeasureTheory ProbabilityTheory Filter Matrix

namespace SRWTightness

/-- The actual tilted reference window has the pair prefactor plus the uniform absolute CLT error. -/
theorem source_pair_tilted_window_bound
    (hKernel : FiniteGaussianBridgeKernelInput) (hGaussian : GaussianEndpointResidualInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (A : ℝ)
      (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : 4 * sourcePairResidualError + 3 + sourceEquilibriumTimeError +
      sourceLowerTimeError ≤ Real.log A)
    (hsmall : (diskEquilibriumWeightConstant / A) / (2 / Real.pi) ≤ 1 / 16)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : t ≤ u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) (At q f : ℝ) (n m l : ℕ)
    (hq : 0 < q) (hf : 0 ≤ f) (hd : 0 < sourceLowerTime (sourceLowerRadius t))
    (hv : sourceLowerTime (sourceLowerRadius t) / 2 ≤
      sourceObservationTime t A I (I - i + 1))
    (hqu : q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))),
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let F := fun j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j)
    let β := pairObservationTilt (Fin.last (I - i))
    let ρ := μ.tilted (fun Y ↦ ∑ j, β j * F j Y)
    let Sigma : Matrix (PairObservationIndex (I - i + 1)) _ ℝ :=
      fun j l ↦ covariance (F j) (F l) μ
    let target := fun j ↦ ∑ l, β l * Sigma j l
    ((ρ.map (fun Y j ↦ F j Y)).prod (independentBridgeLaw ℕ)).real
        (sourcePairWindowEvent t A I i At q f n m l) ≤
      Real.exp (1 / 2) *
        (32 * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2) * (f + l + 1) /
          (sourceLowerTime (sourceLowerRadius t) * (sourceLowerTime (sourceLowerRadius t) -
            sourceObservationTime t A I (I - i + 1)))) +
      sourceTiltApproximationConstant 1 6 (2 * sourceObservationDimensionConstant) (1 / 16) *
        sourceLowerTime (sourceLowerRadius t) ^ 5 / t := by
  filter_upwards [source_pair_window_approximation hBE, eventually_ge_atTop (1 : ℝ)]
    with t happ ht1
  intro b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi u hu k hk At q f n m l
    hq hf hd hv hqu
  have hc := happ b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi u hu k hk
    At q f n m l
  have hg := source_pair_gaussian_window_bound hKernel hGaussian b t A hA ht hlog hsmall
    I hI i hi z y hz hρ hlo hhi u (by linarith) k hk At q f n m l hq hf hd hv hqu
  dsimp only at hc hg ⊢
  simp only [Fin.val_last] at hg
  have hc' := (abs_le.mp hc).2
  linarith

end SRWTightness
