import SRWTightness.SourcePairShellScaledProbabilities
import SRWTightness.SourcePairShellAnnulus

open MeasureTheory ProbabilityTheory Filter

namespace SRWTightness

/-- Counting actual candidates cancels the spatial factors in both shell probability bounds. -/
theorem source_pair_shell_contributions
    (hDisk : LatticeDiskCountInput) (hAnnulus : LatticeAnnulusCountInput)
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
      (hz : ∀ b, (z b : Site) = b)
      (hJoint : ∀ (b : Site) [MeasurableSpace (List (Mark (translateFinset b
        (diskFinset (A * diskEnergyGapRatio ^ I)))))]
        [MeasurableSingletonClass (List (Mark (translateFinset b
          (diskFinset (A * diskEnergyGapRatio ^ I)))))],
        MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (i : ℕ) (hi : i ≤ I),
      let d := sourceLowerTime (sourceLowerRadius t)
      let h := d - sourceObservationTime t A I (I - i + 1)
      let S := sourcePairShell (sourceCandidateAnnulus (Real.exp t)) A i
      let P := sourcePairSuccessWeight t A γ I z
      (h ≤ d / 2 → (∑ p ∈ S, P p) ≤
        C *
          (((1 + h ^ γ) / h) * Real.exp (-2 * h ^ γ))) ∧
      (∑ p ∈ S, P p) ≤ D * (d * Real.exp (-2 * h ^ γ)) := by
  obtain ⟨C, D, hC, hD, happ⟩ :=
    source_pair_shell_scaled_probabilities hPotential hUpper hKernel hGaussian hBE
  obtain ⟨K, hK, hcount⟩ := source_pair_shell_annulus_card hDisk hAnnulus
  refine ⟨K * C, K * D, mul_pos hK hC, mul_pos hK hD, ?_⟩
  filter_upwards [happ, Real.tendsto_exp_atTop.eventually hcount] with t happ hcount
  intro A γ hA ht hAB hmargin I hI z hz hJoint i hi
  let S := sourcePairShell (sourceCandidateAnnulus (Real.exp t)) A i
  let P := sourcePairSuccessWeight t A γ I z
  let d := sourceLowerTime (sourceLowerRadius t)
  let h := d - sourceObservationTime t A I (I - i + 1)
  let a := A * diskEnergyGapRatio ^ i
  have hB := diskEnergyGapRatio_gt_four
  have hpow : 1 ≤ diskEnergyGapRatio ^ i := one_le_pow₀ (by linarith)
  have ha : 1 ≤ a := by dsimp [a]; nlinarith
  have hc : (S.card : ℝ) ≤ K * (Real.exp t) ^ 2 * a ^ 2 := hcount A i ha
  have hm := source_pair_radius_margin A hA hmargin
  have hlog : sourceEquilibriumTimeError + sourceLowerTimeError + 1 ≤ Real.log A := by
    have hn : 0 ≤ sourcePairResidualError := le_max_left _ _
    linarith [hm.1]
  have hb := (source_pair_shell_deficit_bounds t A hA ht hlog I hI).1 i hi
  have hh : 0 < h := by dsimp [h, d]; linarith [hb.1]
  have hd : 0 ≤ d := by dsimp [d]; linarith [hb.1, hb.2]
  have hw : 0 ≤ ((1 + h ^ γ) / h) * Real.exp (-2 * h ^ γ) :=
    mul_nonneg (div_nonneg (add_nonneg (by norm_num) (Real.rpow_nonneg hh.le _)) hh.le)
      (Real.exp_nonneg _)
  have hp (p : Site × Site) (hps : p ∈ S) := by
    letI : MeasurableSpace (List (Mark (translateFinset p.1
      (diskFinset (A * diskEnergyGapRatio ^ I))))) := ⊤
    letI : MeasurableSingletonClass (List (Mark (translateFinset p.1
      (diskFinset (A * diskEnergyGapRatio ^ I))))) := ⟨fun _ ↦ trivial⟩
    exact happ A γ hA ht hAB hmargin I hI z hz i hi p hps (hJoint p.1)
  constructor
  · intro hsmall
    exact pair_shell_sum_cancel S P (Real.exp t) a K C _ (Real.exp_pos t)
      (by linarith) hC.le hw hc (fun p hps ↦ (hp p hps).1 hsmall)
  · exact pair_shell_sum_cancel S P (Real.exp t) a K D _ (Real.exp_pos t)
      (by linarith) hD.le (mul_nonneg hd (Real.exp_nonneg _)) hc (fun p hps ↦ (hp p hps).2)

end SRWTightness
