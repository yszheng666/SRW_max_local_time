import SRWTightness.SourcePairReferenceBandUpper
import SRWTightness.SourcePairDeficitDistance

open MeasureTheory ProbabilityTheory Filter

namespace SRWTightness

/-- The integrated reference bound has the late-pair distance factor at f=h^γ. -/
theorem source_pair_reference_distance_upper
    (hUpper : GWBarrierUpperInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hGaussian : GaussianEndpointResidualInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (A : ℝ)
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
    (γ : ℝ)
    (hv : sourceLowerTime (sourceLowerRadius t) / 2 ≤
      sourceObservationTime t A I (I - i + 1)),
    let d := sourceLowerTime (sourceLowerRadius t)
    let h := d - sourceObservationTime t A I (I - i + 1)
    let ρ := Real.sqrt (normSq ((y : Site) - b))
    let L := (sourceCoarseGeneration t).toNat
    (∫ r in sourceGWCoarseBandEvent t L,
      sourcePairMarkProbability t A b I i z y (geometricGWPopulation r L) (h ^ γ)
        ∂geometricGWRecordLaw 1 L) ≤
      (C / ρ ^ 2) * ((1 + h ^ γ) / h) * Real.exp (-2 * t - 2 * h ^ γ) := by
  obtain ⟨C, hC, happ⟩ := source_pair_reference_band_upper hUpper hKernel hGaussian hBE
  let E := sourceEquilibriumTimeError + sourceLowerTimeError + Real.log (4 * diskEnergyGapRatio)
  refine ⟨C * Real.exp (2 * E), by positivity, ?_⟩
  filter_upwards [happ] with t happ
  intro b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi γ hv
  dsimp only
  let d := sourceLowerTime (sourceLowerRadius t)
  let h := d - sourceObservationTime t A I (I - i + 1)
  let ρ := Real.sqrt (normSq ((y : Site) - b))
  have hh : 0 < h := (source_pair_residual_time b t A sourcePairResidualError hA ht
    (le_max_left _ _) (by linarith) I hI i hi).1
  have hr : 0 < ρ := by dsimp [ρ]; linarith
  have hf : 0 ≤ h ^ γ := Real.rpow_nonneg hh.le _
  have hp := happ b A hA ht hlog hsmall I hI i hi z y hz hρ hlo hhi (h ^ γ) hf hv
  have hdist : |h - Real.log ρ| ≤ E :=
    source_pair_deficit_log_distance b t A ρ hA ht I hI i hi hr hlo hhi
  have hscale : Real.exp (-2 * h) ≤ Real.exp (2 * E) / ρ ^ 2 := by
    have he : Real.exp (2 * Real.log ρ) = ρ ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log hr]
      ring
    calc
      _ ≤ Real.exp (2 * E - 2 * Real.log ρ) :=
        Real.exp_le_exp.mpr (by linarith [(abs_le.mp hdist).1])
      _ = _ := by rw [Real.exp_sub, he]
  have he : Real.exp (-2 * t - 2 * h - 2 * h ^ γ) =
      Real.exp (-2 * h) * Real.exp (-2 * t - 2 * h ^ γ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only at hp
  change _ ≤ C * ((h ^ γ + 1) / h) * Real.exp (-2 * t - 2 * h - 2 * h ^ γ) at hp
  rw [he] at hp
  calc
    _ ≤ C * ((h ^ γ + 1) / h) *
        (Real.exp (-2 * h) * Real.exp (-2 * t - 2 * h ^ γ)) := hp
    _ ≤ C * ((h ^ γ + 1) / h) *
        ((Real.exp (2 * E) / ρ ^ 2) * Real.exp (-2 * t - 2 * h ^ γ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hscale (Real.exp_nonneg _))
        (mul_nonneg hC.le (div_nonneg (by linarith) hh.le))
    _ = _ := by ring

end SRWTightness
