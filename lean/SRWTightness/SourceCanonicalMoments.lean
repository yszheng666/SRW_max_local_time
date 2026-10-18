import SRWTightness.SourceCenteredFullPairBound
import SRWTightness.SourceCanonicalSecondMoment
import SRWTightness.SourceCenteredFirstMoment

open MeasureTheory Filter
namespace SRWTightness

/-- Positive bounded first moment and bounded second moment of the actual successful-site
count, with the existing marked-forest interfaces displayed explicitly. -/
def SourceCanonicalMomentEstimate (A : ℝ) : Prop :=
    ∃ c C D : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      c ≤ (∫ p, sourceCenteredSuccessCount t A (2 / 5) I p ∂sourceEnlargedLaw) ∧
      (∫ p, sourceCenteredSuccessCount t A (2 / 5) I p ∂sourceEnlargedLaw) ≤ C ∧ ∀
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
      (∫ p, sourceCenteredSuccessCount t A (2 / 5) I p ^ 2 ∂sourceEnlargedLaw) ≤ D

/-- Combining the verified five distance contributions proves the actual moment bounds. -/
theorem source_canonical_moment_bounds (J A : ℝ)
    (hTerminal : SourceTerminalEstimate J A (2 / 5))
    (hOne : SourceOnePointEstimate J A (2 / 5))
    (hEarly : SourceMovingEarlyEstimate A) (hFixed : SourceFixedPairsEstimate A (2 / 5))
    (hLater : SourceLateCommonEstimate A (2 / 5)) : SourceCanonicalMomentEstimate A := by
  obtain ⟨c, C, hc, hC, hfirst⟩ :=
    source_centered_first_moment_shared J A (2 / 5) hTerminal hOne
  obtain ⟨D, hD, hfull⟩ := source_centered_full_pair_bound J A hOne hEarly hFixed hLater
  obtain ⟨a, B, hA, hmargin, ha, hB, ht⟩ := hTerminal
  have hA1 : 1 ≤ A := by
    have hh := diskGaussianMinimumRadius_ge_four.trans
      (diskPointGaussianMinimumRadius_ge_base.trans hA)
    linarith only [hh]
  refine ⟨c, C, D, hc, hC, hD, ?_⟩
  filter_upwards [hfirst, hfull, source_canonical_second_moment] with t hfirst hfull hsecond
  obtain ⟨I, hI, hlo, hhi⟩ := hfirst
  refine ⟨I, hI, hlo, hhi, ?_⟩
  intro cm cs clm cls lm ls rm rs fm fs hForest hMix
  rw [hsecond A (2 / 5) hA1 (by norm_num) I hI]
  exact hfull I hI hForest hMix

end SRWTightness
