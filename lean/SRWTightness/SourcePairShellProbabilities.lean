import SRWTightness.SourcePairShellSites
import SRWTightness.SourcePairSuccessChernoff
import SRWTightness.SourcePairRadiusMargin

open MeasureTheory ProbabilityTheory Filter

namespace SRWTightness

/-- Both probability branches hold for every ordered pair in every actual retained shell. -/
theorem source_pair_shell_probabilities
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
      let ρ := Real.sqrt (normSq (p.2 - p.1))
      (h ≤ d / 2 → sourcePairSuccessWeight t A γ I z p ≤
        (C / ρ ^ 2) * ((1 + h ^ γ) / h) * Real.exp (-2 * t - 2 * h ^ γ)) ∧
      sourcePairSuccessWeight t A γ I z p ≤ D * d * Real.exp (-2 * t - 2 * h - 2 * h ^ γ) := by
  obtain ⟨C, hC, hsmall⟩ :=
    source_pair_record_distance_upper hPotential hUpper hKernel hGaussian hBE
  obtain ⟨D, hD, hlarge⟩ := source_pair_success_chernoff hPotential hUpper
  refine ⟨C, D, hC, hD, ?_⟩
  filter_upwards [hsmall, hlarge, source_pair_success_probability_le_record]
    with t hsmall hlarge hsuccess
  intro A γ hA ht hAB hmargin I hI z hz i hi p hp instM instMS hjoint
  obtain ⟨hρ, hmem, hblo, hbhi⟩ := source_pair_shell_sites t A I i hi hAB p hp
  let y : translateFinset p.1 (diskFinset (A * diskEnergyGapRatio ^ I)) := ⟨p.2, hmem⟩
  have hshell := (Finset.mem_filter.mp hp).2
  have hm := source_pair_radius_margin A hA hmargin
  have hlog : sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A := by
    have hn : 0 ≤ sourcePairResidualError := le_max_left _ _
    linarith [hm.1]
  constructor
  · intro hh
    have hv : sourceLowerTime (sourceLowerRadius t) / 2 ≤
        sourceObservationTime t A I (I - i + 1) := by linarith
    have hs := hsuccess A γ p.1 p.2 I I i hA ht hlog hI hi (z p.1) y (z p.2)
      rfl (hz p.2) hblo hbhi
    exact hs.trans (hsmall p.1 A hA ht hm.1 hm.2 I hI i hi (z p.1) y (hz p.1)
      hρ hshell.1 hshell.2 γ hv hblo hbhi hjoint)
  · exact hlarge p.1 A hA ht I hI i hi (z p.1) y (hz p.1) hρ hshell.1 hshell.2
      γ hlog I (z p.2) (hz p.2) hblo hbhi hjoint

end SRWTightness
