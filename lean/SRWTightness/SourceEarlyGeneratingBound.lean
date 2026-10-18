import SRWTightness.RootGeneratingBound
import SRWTightness.SourceEarlyReferenceFactorial
import SRWTightness.SourceEarlyCommonRootMean

open scoped ENNReal
open MeasureTheory Filter
namespace SRWTightness

/-- Equation 8.19 for the actual common reference mark, with finiteness proved. -/
theorem source_early_generating_bound (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hinput : PotentialKernelAsymptoticInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let R := killedRootMeanSup (sourceCommonPairDomain t b j)
        (sourceEntranceDomain m 1 ℓ b ν) (sourceExitDomain m 1 ℓ b ν)
        (sourceEntranceDomain m 1 ℓ w ν) (sourceExitDomain m 1 ℓ w ν)
      let μ := ENNReal.ofReal (∫ Y, ((sourceCommonWordRootCount t b ν Y +
        sourceCommonWordRootCount t w ν Y : ℕ) : ℝ) ∂sourceCommonWordLaw t b w j)
      R ≤ ENNReal.ofReal (C * ((J : ℝ) + 1)) ∧
      ∀ W : ℝ, 0 ≤ W → R * ENNReal.ofReal W < 1 →
      let G := ∫⁻ Y, (1 + ENNReal.ofReal W) ^
        (sourceCommonWordRootCount t b ν Y + sourceCommonWordRootCount t w ν Y)
        ∂sourceCommonWordLaw t b w j
      G ≤ 1 + μ * ENNReal.ofReal W / (1 - R * ENNReal.ofReal W) ∧ G < ∞ := by
  obtain ⟨C, hC, Jf, hf⟩ := source_early_reference_factorial hLast hrec hinput
  obtain ⟨Jp, hp⟩ := source_early_common_root_mean hLast
  refine ⟨C, hC, max Jf Jp, ?_⟩
  intro J₀ hJ₀
  obtain ⟨af, haf, hf⟩ := hf J₀ ((le_max_left _ _).trans hJ₀)
  obtain ⟨ap, hap, hp⟩ := hp J₀ ((le_max_right _ _).trans hJ₀)
  refine ⟨max af ap, haf.trans (le_max_left _ _), ?_⟩
  filter_upwards [hf, hp] with t hf hp
  intro b w hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  have hh := hf b w hbw ((le_max_left _ _).trans ha) hrange
  have hprob := (hp b w hbw ((le_max_right _ _).trans ha) hrange).1
  letI : IsProbabilityMeasure (sourceCommonWordLaw t b w j) := hprob
  refine ⟨hh.1, ?_⟩
  intro W hW hRW
  constructor
  · exact root_generating_bound (sourceCommonWordLaw t b w j)
      (sourceEntranceDomain m 1 ℓ b ν) (sourceExitDomain m 1 ℓ b ν)
      (sourceEntranceDomain m 1 ℓ w ν) (sourceExitDomain m 1 ℓ w ν) _ _ _ hh.2
  · exact root_generating_finite (sourceCommonWordLaw t b w j)
      (sourceEntranceDomain m 1 ℓ b ν) (sourceExitDomain m 1 ℓ b ν)
      (sourceEntranceDomain m 1 ℓ w ν) (sourceExitDomain m 1 ℓ w ν) _ _ _ hh.2
      ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hRW

end SRWTightness
