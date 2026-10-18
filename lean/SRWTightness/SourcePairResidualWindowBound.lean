import SRWTightness.SourcePairIndependentWindowBound
import SRWTightness.SourcePairNodeResidualDensity
import SRWTightness.SourcePairErrorBounds

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual source residual and average correction give a uniform inverse-time pair prefactor. -/
theorem source_pair_residual_window_bound (hKernel : FiniteGaussianBridgeKernelInput)
    (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : 4 * sourcePairResidualError + 1 + sourceEquilibriumTimeError +
      sourceLowerTimeError ≤ Real.log A)
    (hsmall : (diskEquilibriumWeightConstant / A) / (2 / Real.pi) ≤ 1 / 2)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ))
    (q f : ℝ) (l : ℕ) (hq : 0 < q) (hf : 0 ≤ f)
    (hd : 0 < sourceLowerTime (sourceLowerRadius t))
    (hv : sourceLowerTime (sourceLowerRadius t) / 2 ≤
      sourceObservationTime t A I (I - i + 1))
    (hqu : q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
    (a : ((Fin (I - i + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) → Fin 2 → ℝ)
    (ha : Measurable a) :
    let m := sourceLowerRadius t
    let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity m 14
    let μ := markProductLaw D M α k
    let F := normalizedMarkSum M k α (2 / Real.pi) u
    let v := sourceObservationTime t A I (I - i + 1)
    let R := pairResidualMatrix (covariance (F z) (F z) μ) (covariance (F y) (F y) μ)
      (covariance (F z) (F y) μ) v
    let e := geometricDiskPointError b A (Real.exp 1 * m + 14)
      diskEnergyGapRatio (2 / Real.pi) (I + 1)
      (sourcePairAverageIndex I i (Fin.last (I - i)))
    let ν := (gaussianCoordinateLaw (fun j k : Fin (I - i + 1) ↦
      min (sourceObservationTime t A I (j.val + 1))
        (sourceObservationTime t A I (k.val + 1)))).prod (independentBridgeLaw ℕ)
    let s := finiteGaussianPrefixWindow (sourceObservationTime t A I) (I - i + 1) (I + 1)
      (Fin.last (I - i)) q (q - f - l - 1 - 2 * e) (q - f - l - 2 * e)
    (ν.prod (gaussianCoordinateLaw R)).real
      {p | p.1 ∈ s ∧ ∀ j, a p.1 j ≤ p.2 j ∧ p.2 j < a p.1 j + 1} ≤
      32 * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2) * (f + l + 1) /
        (sourceLowerTime m * (sourceLowerTime m - v)) := by
  have hR := source_pair_node_residual_posDef b t A hA ht hlog I hI i hi
    z y hz hρ hlo hhi u hu k hk
  have hden := source_pair_node_residual_density_upper b t A hA ht hlog I hI i hi
    z y hz hρ hlo hhi u hu k hk
  have hh := (source_pair_residual_time b t A sourcePairResidualError hA ht
    (le_max_left _ _) (by linarith) I hI i hi).1
  have he := source_pair_error_bounds b t A hA ht I hI i
  dsimp only at hR hden he ⊢
  have he0 := he.1 (Sum.inl (Fin.last (I - i)))
  have heu := (Finset.single_le_sum (fun j _ ↦ he.1 j)
    (Finset.mem_univ (Sum.inl (Fin.last (I - i))))).trans (he.2.trans hsmall)
  simp only [pairObservationError] at he0 heu
  have hp := source_pair_independent_window_bound hKernel t A I i hA ht hI
    q f _ l hq hf he0 heu hd hv hqu _ hR
    (2 * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2)) _ (by positivity) hh hden a ha
  convert hp using 1 <;> ring

end SRWTightness
