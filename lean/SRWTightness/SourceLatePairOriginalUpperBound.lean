import SRWTightness.SourcePairTerminalUpperBound
import SRWTightness.SourcePairOriginalProbability
import SRWTightness.SourcePairRadiusMargin
import SRWTightness.SourcePairObservationIndex
import SRWTightness.SourceWalkNormalization

open MeasureTheory ProbabilityTheory Filter Matrix

namespace SRWTightness

/-- The original-prefix reference probability at the first covering node and actual terminal count. -/
theorem source_late_pair_original_upper_bound
    (hKernel : FiniteGaussianBridgeKernelInput) (hGaussian : GaussianEndpointResidualInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (b : Site),
      diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      sourcePairLogMargin + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A →
      ∀ (I : ℕ),
      (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) →
      ∀ (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      (z : Site) = b → A < Real.sqrt (normSq ((y : Site) - b)) →
      Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio) →
      ∃ i : ℕ, i ≤ I ∧
      4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i ∧
      A * diskEnergyGapRatio ^ i ≤ 4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)) ∧
      (∀ j : ℕ, j < i → A * diskEnergyGapRatio ^ j < 4 * Real.sqrt (normSq ((y : Site) - b))) ∧
      ∀ (ω : Sample), sourceWalkCoarseBand t b ω →
      let k := sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ω
      let u := Real.sqrt (2 * (k : ℝ))
      let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
      ∀ (f : ℝ), 0 ≤ f →
      sourceLowerTime (sourceLowerRadius t) / 2 ≤
        sourceObservationTime t A I (I - i + 1) →
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let d := sourceLowerTime (sourceLowerRadius t)
    let h := d - sourceObservationTime t A I (I - i + 1)
    (μ.prod (independentBridgeLaw ℕ)).real
      (sourcePairOriginalEvent b t A I i D M z y k α (2 / Real.pi) u
        (sourceTerminalThreshold t u) q f) ≤
      sourcePairReferenceUpperConstant * ((f + 1) / (d * h)) *
        Real.exp (-2 * d - 2 * h - 2 * q - 2 * f) := by
  filter_upwards [source_pair_terminal_upper_bound hKernel hGaussian hBE] with t happ
  intro A b hA ht hmargin I hI z y hz hρ hcut
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  obtain ⟨i, hi, hlo, hhi, hmin⟩ := source_pair_observation_index A
    (Real.sqrt (normSq ((y : Site) - b))) I (by linarith) hρ hcut
  have hm := source_pair_radius_margin A hA hmargin
  refine ⟨i, hi, hlo, hhi, hmin, ?_⟩
  intro ω hband
  dsimp only
  intro f hf hv
  let k := sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ω
  let u := Real.sqrt (2 * (k : ℝ))
  let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
  have hq : Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q ∧
      q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) := hband.2
  have hu : sourceTerminalRoot t q = u := by dsimp [sourceTerminalRoot, q]; ring
  have hk : (sourceTerminalRoot t q) ^ 2 / 2 = (k : ℝ) := by
    rw [hu]
    dsimp [u]
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hp := happ b A hA ht hm.1 hm.2 I hI i hi z y hz (by linarith)
    hlo hhi q hq.1 hq.2 k hk f hf hv
  dsimp only at hp
  rw [hu] at hp
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let μ := markProductLaw D M α k
  have hg := source_pair_observation_geometry b t A hA ht I hI i hi
  have hs := sourceScaleThreshold_conditions t A ha4 ((le_max_left _ _).trans ht)
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith [hs.2.2.1])).1
  letI : IsProbabilityMeasure μ := markProductLaw_isProbabilityMeasure D M α hα.le hg.2.2.2.2 k
  have he := source_pair_original_probability b t A I i hA ht hI D M z y k α
    (2 / Real.pi) u (sourceTerminalThreshold t u) q f μ
  exact he.trans_le hp

end SRWTightness
