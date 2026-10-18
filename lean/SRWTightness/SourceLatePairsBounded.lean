import SRWTightness.SourcePairShellContributions
import SRWTightness.SourcePairShellChernoffUniform
import SRWTightness.SourcePairShellSum

open MeasureTheory ProbabilityTheory Filter

namespace SRWTightness

/-- The full late-distance ordered-pair contribution is uniformly bounded on the actual SRW space. -/
theorem source_late_pairs_bounded
    (hSum : SeparatedStretchedExponentialSumInput)
    (hBound : QuadraticStretchedExponentialBoundInput)
    (γ : ℝ) (hγ : 0 < γ)
    (hDisk : LatticeDiskCountInput) (hAnnulus : LatticeAnnulusCountInput)
    (hPotential : PotentialKernelAsymptoticInput) (hUpper : GWBarrierUpperInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hGaussian : GaussianEndpointResidualInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ)
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
      ,
      (∑ p ∈ sourceLatePairs (sourceCandidateAnnulus (Real.exp t)) A I,
        sourcePairSuccessWeight t A γ I z p) ≤ C := by
  obtain ⟨C, D, hC, hD, hshell⟩ :=
    source_pair_shell_contributions hDisk hAnnulus hPotential hUpper hKernel hGaussian hBE
  obtain ⟨L, hL, hlow⟩ := source_pair_shell_series_bound hSum 2 γ (by norm_num) hγ
  obtain ⟨H, hH, hhigh⟩ := source_pair_shell_chernoff_uniform hBound γ hγ
  refine ⟨C * L + D * H, by positivity, ?_⟩
  filter_upwards [hshell] with t hshell
  intro A hA ht hAB hmargin I hI z hz hJoint
  let d := sourceLowerTime (sourceLowerRadius t)
  let h := fun i ↦ d - sourceObservationTime t A I (I - i + 1)
  let W := fun i ↦ ((1 + (h i) ^ γ) / h i) * Real.exp (-2 * (h i) ^ γ)
  let V := fun i ↦ if d / 2 < h i then d * Real.exp (-2 * (h i) ^ γ) else 0
  let P := sourcePairSuccessWeight t A γ I z
  have ha : 0 < A := by linarith [diskEnergyGapRatio_gt_four]
  have hm := source_pair_radius_margin A hA hmargin
  have hlog : sourceEquilibriumTimeError + sourceLowerTimeError + 1 ≤ Real.log A := by
    have hn : 0 ≤ sourcePairResidualError := le_max_left _ _
    linarith [hm.1]
  have hw (i : ℕ) (hi : i ≤ I) : 0 ≤ W i := by
    have hh := ((source_pair_shell_deficit_bounds t A hA ht hlog I hI).1 i hi).1
    have hh0 : 0 ≤ h i := by dsimp [h, d]; linarith
    exact mul_nonneg (div_nonneg (add_nonneg (by norm_num) (Real.rpow_nonneg hh0 _)) hh0)
      (Real.exp_nonneg _)
  have hpoint (i : ℕ) (hi : i ∈ Finset.range (I + 1)) :
      (∑ p ∈ sourcePairShell (sourceCandidateAnnulus (Real.exp t)) A i, P p) ≤
        C * W i + D * V i := by
    have hii : i ≤ I := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hp := hshell A γ hA ht hAB hmargin I hI z hz hJoint i hii
    by_cases hh : d / 2 < h i
    · have hh' := hp.2.trans (le_add_of_nonneg_left (mul_nonneg hC.le (hw i hii)))
      simpa only [V, if_pos hh] using hh'
    · simpa only [V, if_neg hh, mul_zero, add_zero] using hp.1 (le_of_not_gt hh)
  have hl : (∑ i ∈ Finset.range (I + 1), W i) ≤ L := hlow t A hA ht hlog I hI
  have hv : (∑ i ∈ Finset.range (I + 1), V i) ≤ H := hhigh t A hA ht hlog I hI
  calc
    _ ≤ ∑ i ∈ Finset.range (I + 1), ∑ p ∈ sourcePairShell
        (sourceCandidateAnnulus (Real.exp t)) A i, P p :=
      source_late_pair_sum_le_shells _ A I ha P (sourcePairSuccessWeight_nonneg t A γ I z)
    _ ≤ ∑ i ∈ Finset.range (I + 1), (C * W i + D * V i) := Finset.sum_le_sum hpoint
    _ = C * (∑ i ∈ Finset.range (I + 1), W i) +
        D * (∑ i ∈ Finset.range (I + 1), V i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hl hC.le)
      (mul_le_mul_of_nonneg_left hv hD.le)

end SRWTightness
