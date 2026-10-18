import SRWTightness.SourceCenteredLateCommon
import SRWTightness.SourceCenteredClosePairs

open MeasureTheory Filter
namespace SRWTightness

/-- All actual candidate-pair contributions are uniformly bounded using the common radius
and the five distance ranges already certified on the original probability space. -/
theorem source_centered_full_pair_bound (J A : ℝ)
    (hOne : SourceOnePointEstimate J A (2 / 5))
    (hEarly : SourceMovingEarlyEstimate A) (hFixed : SourceFixedPairsEstimate A (2 / 5))
    (hLater : SourceLateCommonEstimate A (2 / 5)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) → ∀
      [∀ j : ℕ, MeasurableSpace (FiniteExcursionRecord WordMark j)]
      [∀ j : ℕ, MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
      [∀ j : ℕ, MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
      [∀ j : ℕ, MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))]
      [∀ b : Site, MeasurableSpace
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ b : Site, MeasurableSingletonClass
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ (b : Site) (ν : ℕ), MeasurableSpace
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ (b : Site) (ν : ℕ), MeasurableSingletonClass
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ (b : Site) (ν : ℕ), MeasurableSpace (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [∀ (b : Site) (ν : ℕ), MeasurableSingletonClass (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      (hForest : ∀ b : Site, b ∈ sourceCandidateAnnulus (Real.exp t) →
        MarkedGWForestJointInput
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hMix : ∀ (b w : Site) (ν : ℕ), b ∈ sourceCandidateAnnulus (Real.exp t) →
        w ∈ sourceCandidateAnnulus (Real.exp t) → b ≠ w →
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)),
      sourceCenteredPairContribution t A (2 / 5) I ≤ C := by
  obtain ⟨E, a₀, hA, hE, ha₀, he⟩ := hEarly
  obtain ⟨hA', hfixed⟩ := hFixed
  obtain ⟨F, hF, hf⟩ := hfixed a₀
  obtain ⟨L, hL, hl⟩ := hLater
  obtain ⟨B, hB, hb⟩ := source_centered_close_pairs_bounded J A (2 / 5) (by norm_num) hOne
  refine ⟨B + L + F + E, by positivity, ?_⟩
  filter_upwards [he, hf, hl, hb, source_full_pair_sum_bound] with t he hf hl hb hcover
  intro I hI cm cs clm cls lm ls rm rs fm fs hForest hMix
  let P := fun p : Site × Site ↦ sourceEnlargedLaw.real
    (sourceCenteredSuccessEvent t A (2 / 5) p.1 I ∩
      sourceCenteredSuccessEvent t A (2 / 5) p.2 I)
  have ha : 0 < A := lt_of_lt_of_le (by
    linarith [diskGaussianMinimumRadius_ge_four])
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have htotal := hcover A I a₀ ha hI P (fun _ ↦ measureReal_nonneg)
  have hmove := he I hI hForest hMix
  have hfix := hf I hI hForest hMix
  have hlate := hl I hI
  have hclose := hb I hI
  change (∑ p ∈ sourceClosePairs (sourceCandidateAnnulus (Real.exp t)) A, P p) ≤ B at hclose
  change (∑ p ∈ sourceFixedDistancePairs t a₀, P p) ≤ F at hfix
  change (∑ p ∈ sourceLatePairs (sourceCandidateAnnulus (Real.exp t)) A I, P p) +
    (∑ j ∈ sourceCommonLevels t,
      ∑ p ∈ sourceCommonPairs (sourceCandidateAnnulus (Real.exp t)) t j, P p) ≤ L at hlate
  change (∑ a ∈ Finset.Ico a₀ (sourceCoarseLowerLevel t + sourceCommonPairGap t),
    ∑ p ∈ sourceDistancePairs (sourceCandidateAnnulus (Real.exp t)) t a, P p) ≤ E at hmove
  rw [source_centered_pair_contribution_product]
  change (∑ p ∈ (sourceCandidateAnnulus (Real.exp t)).product
    (sourceCandidateAnnulus (Real.exp t)), P p) ≤ _
  dsimp only at htotal
  linarith only [htotal, hmove, hfix, hlate, hclose]

end SRWTightness
