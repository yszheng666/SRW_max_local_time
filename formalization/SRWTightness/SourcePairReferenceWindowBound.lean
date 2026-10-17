import SRWTightness.SourcePairTiltedWindowUniform
import SRWTightness.PairWindowInverseProbability
import SRWTightness.SourcePairNodeCumulant

open MeasureTheory ProbabilityTheory Filter Matrix

namespace SRWTightness

/-- Each actual reference window has the pair prefactor and its full inverse-tilt weight. -/
theorem source_pair_reference_window_bound
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
    (hqu : q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
    (ε : ℝ) (hAt : 2 * sourceLowerTime (sourceLowerRadius t) + q - ε ≤ At),
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let F := fun j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j)
    let β := pairObservationTilt (Fin.last (I - i))
    let ρ := μ.tilted (fun Y ↦ ∑ j, β j * F j Y)
    let C := 1 + 4 * sourcePairVarianceError +
      4 * (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 +
        Real.log (4 * diskEnergyGapRatio)) + 1 / (2 / Real.pi)
    ((μ.map (fun Y j ↦ F j Y)).prod (independentBridgeLaw ℕ)).real
      (sourcePairWindowEvent t A I i At q f n m l) ≤
      (Real.exp (C + 4 * ε) *
        Real.exp (-2 * sourceLowerTime (sourceLowerRadius t) -
          2 * (sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)) -
          2 * q - 2 * f) *
        ((Real.exp (-2)) ^ n * (Real.exp (-2)) ^ m * (Real.exp (-2)) ^ l)) *
      ((Real.exp (1 / 2) * 32 * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2) + 1) * (f + l + 1) /
        (sourceLowerTime (sourceLowerRadius t) * (sourceLowerTime (sourceLowerRadius t) -
          sourceObservationTime t A I (I - i + 1)))) := by
  filter_upwards [source_pair_tilted_window_uniform hKernel hGaussian hBE,
    source_pair_tilt_approximation hBE, source_pair_node_cumulant] with t happ hprob hcgf
  intro b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi u hu k hk At q f n m l
    hq hf hd hv hqu ε hAt
  dsimp only
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let μ := markProductLaw D M α k
  let F := fun j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
    (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j)
  let β := pairObservationTilt (Fin.last (I - i))
  let ρ := μ.tilted (fun Y ↦ ∑ j, β j * F j Y)
  let X := fun Y ↦ ∑ j, β j * F j Y
  let C := 1 + 4 * sourcePairVarianceError +
    4 * (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 +
      Real.log (4 * diskEnergyGapRatio)) + 1 / (2 / Real.pi)
  have hg := source_pair_observation_geometry b t A hA ht I hI i hi
  have hs := sourceScaleThreshold_conditions t A
    (diskGaussianMinimumRadius_ge_four.trans (diskPointGaussianMinimumRadius_ge_base.trans hA))
    ((le_max_left _ _).trans ht)
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith [hs.2.2.1])).1
  letI : IsProbabilityMeasure μ := markProductLaw_isProbabilityMeasure D M α hα.le hg.2.2.2.2 k
  letI : IsProbabilityMeasure (μ.tilted X) :=
    (hprob b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi u hu k hk).1
  have hX : Integrable (fun Y ↦ Real.exp (X Y)) μ := by
    by_contra hnot
    have hh := congrArg (fun ν : Measure (MarkSamples M k) ↦ ν Set.univ)
      (tilted_of_not_integrable hnot)
    simpa using hh
  have hstat : X = (2 : ℝ) •
      (normalizedMarkSum M k α (2 / Real.pi) u z +
        normalizedMarkSum M k α (2 / Real.pi) u y -
        normalizedEquilibriumAverage D M
          (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ i))) k α (2 / Real.pi) u) := by
    funext Y
    change (∑ j, pairObservationTilt (Fin.last (I - i)) j *
      normalizedWeightedSum M k α (2 / Real.pi) u
        (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j) Y) = _
    rw [pairObservationTilt_statistic, sourcePairAverageFamily_last b A I i hi]
    rfl
  have hc := hcgf A b hA ht I hI i hi z y hz hρ hlo hhi u hu k hk
  have hΛ : cgf X μ 1 ≤ 4 * sourceLowerTime (sourceLowerRadius t) -
      2 * sourceObservationTime t A I (I - i + 1) + C := by
    rw [hstat]
    have hc' := (abs_le.mp hc).2
    dsimp [C]
    linarith
  have hF : Measurable (fun Y j ↦ F j Y) := by
    dsimp [F]
    unfold normalizedWeightedSum normalizedMarkSum
    fun_prop
  have hinv := pair_window_inverse_probability μ (independentBridgeLaw ℕ)
    (Fin.last (I - i)) (fun Y j ↦ F j Y) hF At (sourceLowerTime (sourceLowerRadius t))
    (sourceObservationTime t A I (I - i + 1)) q f C ε n m l hX hΛ hAt
    (sourcePairWindowEvent t A I i At q f n m l)
    (sourcePairWindowEvent_measurable t A I i At q f n m l) (fun _ hp ↦ hp.1)
  have htilt := happ b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi u hu k hk
    At q f n m l hq hf hd hv hqu
  exact hinv.trans (mul_le_mul_of_nonneg_left htilt (by positivity))

end SRWTightness
