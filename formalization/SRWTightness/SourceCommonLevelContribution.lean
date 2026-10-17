import SRWTightness.SourceCommonPairCount
import SRWTightness.SourceCommonSuccessProbability
import SRWTightness.SourceCommonExponentLower
import SRWTightness.CommonSpatialCancellation
import SRWTightness.SourcePairShellSites

open MeasureTheory Filter
open scoped BigOperators
namespace SRWTightness

/-- Equation (9.14): all actual candidate pairs at one common level contribute at most Ct^26 e^-2w. -/
theorem source_common_level_contribution (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) (hpot : PotentialKernelAsymptoticInput)
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (hJoint : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWJointInput (Mark K)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (I j : ℕ)
      (z : ∀ b : Site, translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      (∀ b, (z b : Site) = b) → sourceCoarseLowerLevel t ≤ j →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      (∑ p ∈ sourceCommonPairs (sourceCandidateAnnulus (Real.exp t)) t j,
        sourcePairSuccessWeight t A γ I z p) ≤
        C * t ^ 26 * Real.exp (-2 * (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)) := by
  classical
  obtain ⟨K, hK, hc⟩ := source_common_pairs_annulus_card hDisk hAnnulus
  obtain ⟨C, hC, hp⟩ := source_common_success_probability_upper hpot hGW hOcc hRes hJoint
  obtain ⟨E, hE, he⟩ := source_common_exponent_lower
  refine ⟨K * C * Real.exp (E + 12), by positivity, ?_⟩
  filter_upwards [hc, hp, he, sourceCoarseLowerLevel_eventually_twenty,
    eventually_ge_atTop (1 : ℝ)] with t hc hp he hcut ht
  intro A γ I j z hz hj hd
  have hj1 : 1 ≤ j := by omega
  let wj := (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)
  let S := sourceCommonPairs (sourceCandidateAnnulus (Real.exp t)) t j
  let Q := C * t ^ 2 * Real.exp
    (-4 * t + 2 * (j : ℝ) - 2 * wj + 4 * Real.log t + 4 * (sourceCommonPairGap t : ℝ) + E)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hpoint (p : Site × Site) (hps : p ∈ S) : sourcePairSuccessWeight t A γ I z p ≤ Q := by
    obtain ⟨hZ, hne, hi⟩ := Finset.mem_filter.mp hps
    have hb := (mem_sourceCandidateAnnulus (Real.exp t) (Real.exp_pos _) p.1).mp
      (Finset.mem_product.mp hZ).1
    have hprob := hp p.1 p.2 j hne hj hi hd hb.1 hb.2 A γ I I (z p.1) (z p.2)
      (hz p.1) (hz p.2)
    have hexponent := he p.1 p.2 j hne hj1 hi hd
    have hexp := Real.exp_le_exp.mpr (show
        -(sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
          (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 /
            sourceCommonPairRowScale t p.1 p.2 j ≤
        -4 * t + 2 * (j : ℝ) - 2 * wj + 4 * Real.log t +
          4 * (sourceCommonPairGap t : ℝ) + E by
      dsimp [wj]
      simp only [neg_div]
      linarith)
    exact hprob.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hsum : (∑ p ∈ S, sourcePairSuccessWeight t A γ I z p) ≤ (S.card : ℝ) * Q := by
    calc
      _ ≤ ∑ p ∈ S, Q := Finset.sum_le_sum hpoint
      _ = _ := by simp
  have hcount : (S.card : ℝ) ≤ K * Real.exp
      (4 * t - 2 * (j : ℝ) - 2 * (sourceCommonPairGap t : ℝ)) := hc j
  have hh := hsum.trans (mul_le_mul_of_nonneg_right hcount hQ)
  have hcancel := common_spatial_cancellation t (j : ℝ) (sourceCommonPairGap t : ℝ) wj E
    (by linarith) (sourceCommonPairGap_bounds t ht).2.le
  calc
    _ ≤ (K * Real.exp (4 * t - 2 * (j : ℝ) - 2 * (sourceCommonPairGap t : ℝ))) * Q := hh
    _ = (K * C) * (Real.exp (4 * t - 2 * (j : ℝ) - 2 * (sourceCommonPairGap t : ℝ)) *
        (t ^ 2 * Real.exp (-4 * t + 2 * (j : ℝ) - 2 * wj + 4 * Real.log t +
          4 * (sourceCommonPairGap t : ℝ) + E))) := by dsimp [Q]; ring
    _ ≤ (K * C) * (Real.exp (E + 12) * t ^ 26 * Real.exp (-2 * wj)) :=
      mul_le_mul_of_nonneg_left hcancel (by positivity)
    _ = _ := by dsimp [wj]; ring

end SRWTightness
