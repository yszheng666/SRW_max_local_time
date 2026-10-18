import SRWTightness.RootRealExponentialBound
import SRWTightness.SourceEarlyReferenceFactorial
import SRWTightness.SourceEarlyCommonRootMean

open scoped ENNReal
open MeasureTheory Filter
namespace SRWTightness

/-- The actual common reference mark has an integrable real exponential and exact mean term. -/
theorem source_early_single_mark_log_moment (hLast : FiniteLastVisitCountInput)
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
      let N := fun Y ↦ sourceCommonWordRootCount t b ν Y + sourceCommonWordRootCount t w ν Y
      let P := sourceCommonWordLaw t b w j
      let μ := ∫ Y, (N Y : ℝ) ∂P
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → (C * ((J : ℝ) + 1)) * s ≤ 1 / 4 →
        Integrable (fun Y ↦ Real.exp (s * (N Y : ℝ))) P ∧
        1 ≤ (∫ Y, Real.exp (s * (N Y : ℝ)) ∂P) ∧
        Real.log (∫ Y, Real.exp (s * (N Y : ℝ)) ∂P) ≤
          μ * s + μ * (2 + 8 * (C * ((J : ℝ) + 1))) * s ^ 2 := by
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
  let P := sourceCommonWordLaw t b w j
  let N := fun Y ↦ sourceCommonWordRootCount t b ν Y + sourceCommonWordRootCount t w ν Y
  let μ : ℝ := ∫ Y, (N Y : ℝ) ∂P
  let Q : ℝ := C * ((J : ℝ) + 1)
  have hh := hf b w hbw ((le_max_left _ _).trans ha) hrange
  have hprob := (hp b w hbw ((le_max_right _ _).trans ha) hrange).1
  letI : IsProbabilityMeasure P := hprob
  have hμ : 0 ≤ μ := integral_nonneg (fun Y ↦ Nat.cast_nonneg _)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  intro s hs hsmall hQs
  apply root_real_exponential_bound P
    (sourceEntranceDomain m 1 ℓ b ν) (sourceExitDomain m 1 ℓ b ν)
    (sourceEntranceDomain m 1 ℓ w ν) (sourceExitDomain m 1 ℓ w ν)
    μ Q s hμ hQ hs hsmall hQs
  intro p
  exact (hh.2 p).trans (mul_le_mul_left' (pow_le_pow_left' hh.1 p) _)

end SRWTightness
