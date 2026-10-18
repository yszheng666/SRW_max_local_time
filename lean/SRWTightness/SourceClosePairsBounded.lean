import SRWTightness.SourceOnePoint
import SRWTightness.SourceClosePairContribution

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- Manuscript (9.1): actual bounded-distance ordered pairs have a uniform finite contribution. -/
theorem source_close_pairs_bounded (hPotential : PotentialKernelAsymptoticInput)
    (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (hLattice : LatticeAnnulusCountInput)
    (hJoint : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWJointInput (Mark K)) :
    ∃ A K : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < K ∧
      ∀ᶠ R : ℝ in atTop,
      ∃ (I : sourceCandidateAnnulus R → ℕ)
        (z : ∀ b : sourceCandidateAnnulus R,
          translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b))),
      (∀ b : sourceCandidateAnnulus R, (z b : Site) = (b : Site)) ∧
      (∀ (b : sourceCandidateAnnulus R) (i : ℕ),
        A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 ↔ i ≤ I b) ∧
      sourceClosePairContribution R A γ I z ≤ K := by
  obtain ⟨A, c, C, c₁, C₁, hA, hc, hC, hc₁, hC₁, hone⟩ := source_onepoint
    hPotential hLower hUpper hReconstruct hBE hGaussian hReflection hBridge hReverse
    hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf hLattice hJoint
  let D : ℝ := (diskFinset (|A| + 1)).card
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨A, 1 + D * C₁, hA, by positivity, ?_⟩
  filter_upwards [hone, Real.tendsto_log_atTop.eventually
    source_local_time_success_nullMeasurable, eventually_gt_atTop (0 : ℝ)]
    with R hone hn hR
  obtain ⟨I, z, hz, hI, hp, hlo, hhi⟩ := hone
  refine ⟨I, z, hz, hI, ?_⟩
  have hs (b : sourceCandidateAnnulus R) :
      NullMeasurableSet (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b))
        sourceEnlargedLaw := by
    have hb := (mem_sourceCandidateAnnulus R hR b).mp b.property
    have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
      (diskPointGaussianMinimumRadius_ge_base.trans hA)
    have hpow : 1 ≤ diskEnergyGapRatio ^ I b :=
      one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
    have ha : 1 ≤ A * diskEnergyGapRatio ^ I b := by nlinarith
    apply source_site_success_nullMeasurable
    exact hn A γ b (I b) (z b) hγ ha ((hI b (I b)).mpr le_rfl)
      (by simpa only [Real.exp_log hR] using hb.1)
      (by simpa only [Real.exp_log hR] using hb.2)
  have hh := source_close_pair_first_moment R A γ I z hs
  have hmul := mul_le_mul_of_nonneg_left hhi hD
  change sourceClosePairContribution R A γ I z ≤ D * _ at hh
  exact (hh.trans hmul).trans (by linarith)

end SRWTightness
