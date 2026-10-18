import SRWTightness.SourcePairReferenceWindowBound
import SRWTightness.SourcePairWindowSum

open MeasureTheory ProbabilityTheory Filter Matrix

namespace SRWTightness

/-- The complete reference pair event has the pair prefactor after summing every unit window. -/
theorem source_pair_reference_upper_bound
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
    (u : ℝ) (hu : t ≤ u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) (At q f : ℝ)
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
    let C := 1 + 4 * sourcePairVarianceError +
      4 * (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 +
        Real.log (4 * diskEnergyGapRatio)) + 1 / (2 / Real.pi)
    let B := Real.exp (1 / 2) * 32 * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2) + 1
    let d := sourceLowerTime (sourceLowerRadius t)
    let h := d - sourceObservationTime t A I (I - i + 1)
    ((μ.map (fun Y j ↦ F j Y)).prod (independentBridgeLaw ℕ)).real
      (sourcePairUpperEvent t A I i At q f) ≤
      (Real.exp (C + 4 * ε) * B / (1 - Real.exp (-2)) ^ 4) *
        ((f + 1) / (d * h)) * Real.exp (-2 * d - 2 * h - 2 * q - 2 * f) := by
  filter_upwards [source_pair_reference_window_bound hKernel hGaussian hBE] with t happ
  intro b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi u hu k hk At q f
    hq hf hd hv hqu ε hAt
  dsimp only
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let μ := markProductLaw D M α k
  let F := fun j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
    (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j)
  let C := 1 + 4 * sourcePairVarianceError +
    4 * (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 +
      Real.log (4 * diskEnergyGapRatio)) + 1 / (2 / Real.pi)
  let B := Real.exp (1 / 2) * 32 * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2) + 1
  let d := sourceLowerTime (sourceLowerRadius t)
  let h := d - sourceObservationTime t A I (I - i + 1)
  let r := Real.exp (-2)
  let E0 := Real.exp (C + 4 * ε) * Real.exp (-2 * d - 2 * h - 2 * q - 2 * f)
  let W := E0 * B / (d * h)
  have hg := source_pair_observation_geometry b t A hA ht I hI i hi
  have hs := sourceScaleThreshold_conditions t A
    (diskGaussianMinimumRadius_ge_four.trans (diskPointGaussianMinimumRadius_ge_base.trans hA))
    ((le_max_left _ _).trans ht)
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith [hs.2.2.1])).1
  letI : IsProbabilityMeasure μ := markProductLaw_isProbabilityMeasure D M α hα.le hg.2.2.2.2 k
  have hF : Measurable (fun Y j ↦ F j Y) := by
    dsimp [F]
    unfold normalizedWeightedSum normalizedMarkSum
    fun_prop
  letI : IsProbabilityMeasure (μ.map (fun Y j ↦ F j Y)) :=
    Measure.isProbabilityMeasure_map hF.aemeasurable
  let ν := (μ.map (fun Y j ↦ F j Y)).prod (independentBridgeLaw ℕ)
  have hh : 0 < h := (source_pair_residual_time b t A sourcePairResidualError hA ht
    (le_max_left _ _) (by linarith) I hI i hi).1
  have hW : 0 ≤ W := by dsimp [W, E0, B]; positivity
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hbound (n m l : ℕ) : ν.real (sourcePairWindowEvent t A I i At q f n m l) ≤
      W * (r ^ n * (r ^ m * (r ^ l * (f + l + 1)))) := by
    have hp := happ b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi u hu k hk
      At q f n m l hq hf hd hv hqu ε hAt
    dsimp only at hp
    convert hp using 1
    dsimp [W, E0, B, r, d, h, C]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  have hsum := source_pair_window_sum t A I i At q f r W ν hf hr0 hr1 hW hbound
  convert hsum using 1
  dsimp [W, E0, B, r, d, h, C]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

end SRWTightness
