import SRWTightness.SourceFullPairSum
import SRWTightness.SourceLatePairsBounded
import SRWTightness.SourceCommonTotalContribution
import SRWTightness.SourcePairCenterChoice

open MeasureTheory Filter
namespace SRWTightness

/-- Uniform bounds for the two later-distance contributions at a specified radius. -/
def SourceLateCommonEstimate (A γ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ I : ℕ,
    (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
    let P := fun p : Site × Site ↦ sourceEnlargedLaw.real
      (sourceCenteredSuccessEvent t A γ p.1 I ∩ sourceCenteredSuccessEvent t A γ p.2 I)
    (∑ p ∈ sourceLatePairs (sourceCandidateAnnulus (Real.exp t)) A I, P p) +
      (∑ j ∈ sourceCommonLevels t,
        ∑ p ∈ sourceCommonPairs (sourceCandidateAnnulus (Real.exp t)) t j, P p) ≤ C

/-- Existing late/common bounds hold simultaneously for the prescribed common radius. -/
theorem source_centered_late_common_bounded
    (hSum : SeparatedStretchedExponentialSumInput)
    (hBound : QuadraticStretchedExponentialBoundInput)
    (γ : ℝ) (hγ : 0 < γ)
    (hDisk : LatticeDiskCountInput) (hAnnulus : LatticeAnnulusCountInput)
    (hPotential : PotentialKernelAsymptoticInput) (hUpper : GWBarrierUpperInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hGaussian : GaussianEndpointResidualInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (hJoint : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWJointInput (Mark K))
    (A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A)
    (hAB : 4 * diskEnergyGapRatio ≤ A)
    (hmargin : sourcePairLogMargin + sourceEquilibriumTimeError + sourceLowerTimeError ≤
      Real.log A) : SourceLateCommonEstimate A γ := by
  obtain ⟨L, hL, hl⟩ := source_late_pairs_bounded hSum hBound γ hγ hDisk hAnnulus
    hPotential hUpper hKernel hGaussian hBE
  obtain ⟨C, hC, hc⟩ := source_common_total_contribution hDisk hAnnulus hPotential hGW
    hOcc hRes hJoint
  refine ⟨L + C, add_pos hL hC, ?_⟩
  filter_upwards [hl, hc, eventually_ge_atTop (sourceGaussianThreshold A),
    eventually_ge_atTop (1 : ℝ)] with t hl hc htA ht
  intro I hI
  have ha : 0 < A := by linarith [diskEnergyGapRatio_gt_four]
  obtain ⟨z, hz⟩ := source_pair_center_choice A I ha
  have hlate := hl A hA htA hAB hmargin I hI z hz
    (fun b _ _ ↦ hJoint (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
  have hcommon := hc A γ I z hz
  have hdecay : C / t ^ 1973 ≤ C := div_le_self hC.le (one_le_pow₀ ht)
  simp_rw [source_pair_success_weight_eq_centered t A γ I z hz] at hlate hcommon
  exact add_le_add hlate (hcommon.trans hdecay)

end SRWTightness
