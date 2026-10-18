import SRWTightness.SourcePairShellProbabilities
import SRWTightness.PairShellProbabilityScale
import SRWTightness.SourcePairShellGeometry

open MeasureTheory ProbabilityTheory Filter

namespace SRWTightness

/-- Both actual shell probability branches have the inverse area factor used in spatial counting. -/
theorem source_pair_shell_scaled_probabilities
    (hPotential : PotentialKernelAsymptoticInput) (hUpper : GWBarrierUpperInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hGaussian : GaussianEndpointResidualInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ)
      (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
      (hAB : 4 * diskEnergyGapRatio ≤ A)
      (hmargin : sourcePairLogMargin + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A)
      (I : ℕ)
      (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
      (z : ∀ b : Site, translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
      (hz : ∀ b, (z b : Site) = b) (i : ℕ) (hi : i ≤ I) (p : Site × Site)
      (hp : p ∈ sourcePairShell (sourceCandidateAnnulus (Real.exp t)) A i),
      ∀ [MeasurableSpace (List (Mark (translateFinset p.1
        (diskFinset (A * diskEnergyGapRatio ^ I)))))]
        [MeasurableSingletonClass (List (Mark (translateFinset p.1
          (diskFinset (A * diskEnergyGapRatio ^ I)))))],
      MarkedGWJointInput (Mark (translateFinset p.1 (diskFinset (A * diskEnergyGapRatio ^ I)))) →
      let d := sourceLowerTime (sourceLowerRadius t)
      let h := d - sourceObservationTime t A I (I - i + 1)
      let a := A * diskEnergyGapRatio ^ i
      (h ≤ d / 2 → sourcePairSuccessWeight t A γ I z p ≤
        (C / ((Real.exp t) ^ 2 * a ^ 2)) *
          (((1 + h ^ γ) / h) * Real.exp (-2 * h ^ γ))) ∧
      sourcePairSuccessWeight t A γ I z p ≤ (D / ((Real.exp t) ^ 2 * a ^ 2)) * (d * Real.exp (-2 * h ^ γ)) := by
  obtain ⟨C, D, hC, hD, happ⟩ :=
    source_pair_shell_probabilities hPotential hUpper hKernel hGaussian hBE
  let E := sourceEquilibriumTimeError + sourceLowerTimeError
  have hB : 0 < 4 * diskEnergyGapRatio := by linarith [diskEnergyGapRatio_gt_four]
  refine ⟨C * (4 * diskEnergyGapRatio) ^ 2, D * Real.exp (2 * E),
    mul_pos hC (sq_pos_of_pos hB), mul_pos hD (Real.exp_pos _), ?_⟩
  filter_upwards [happ] with t happ
  intro A γ hA ht hAB hmargin I hI z hz i hi p hp instM instMS hjoint
  have hs := happ A γ hA ht hAB hmargin I hI z hz i hi p hp hjoint
  have hm := source_pair_radius_margin A hA hmargin
  have hlog : sourceEquilibriumTimeError + sourceLowerTimeError + 1 ≤ Real.log A := by
    have hn : 0 ≤ sourcePairResidualError := le_max_left _ _
    linarith [hm.1]
  have hb := (source_pair_shell_deficit_bounds t A hA ht hlog I hI).1 i hi
  have hsite := source_pair_shell_sites t A I i hi hAB p hp
  have ha : 0 < A * diskEnergyGapRatio ^ i :=
    mul_pos (by linarith) (pow_pos (by linarith [diskEnergyGapRatio_gt_four]) _)
  have hh : 0 < sourceLowerTime (sourceLowerRadius t) -
      sourceObservationTime t A I (I - i + 1) := by linarith [hb.1]
  have hd : 0 ≤ sourceLowerTime (sourceLowerRadius t) := by linarith [hb.1, hb.2]
  constructor
  · intro hsmall
    apply pair_shell_distance_probability_scale _ C _ t _ _ _ (4 * diskEnergyGapRatio)
      hC.le _ ha (by linarith [hsite.1]) hB.le (Finset.mem_filter.mp hp).2.2 (hs.1 hsmall)
    exact div_nonneg (add_nonneg (by norm_num) (Real.rpow_nonneg hh.le _)) hh.le
  · exact pair_shell_chernoff_probability_scale _ D _ t _ _ _ E hD.le hd ha
      (source_pair_deficit_log_radius 0 t A hA ht I hI i hi) hs.2

end SRWTightness
