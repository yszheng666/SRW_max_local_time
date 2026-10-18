import SRWTightness.SourceEarlyCommonObservation
import SRWTightness.SourceEarlyCommonIntensity
import SRWTightness.ReferenceIntegral

open MeasureTheory Filter
namespace SRWTightness

/-- The actual common reference mark at the early distance-dependent level is a probability law
with constant coordinate mean equal to the intensity in equation 8.13. -/
theorem source_early_common_reference_mean :
    ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      IsProbabilityMeasure (referenceMarkLaw (sourceCommonPairDomain t b j)
        (sourceCommonPairObservation b w) (sourceCommonPairIntensity t j)) ∧
      (∀ z : sourceCommonPairObservation b w,
        ∫ Y, (Y z : ℝ) ∂referenceMarkLaw (sourceCommonPairDomain t b j)
          (sourceCommonPairObservation b w) (sourceCommonPairIntensity t j) =
            sourceCommonPairIntensity t j) ∧
      |sourceCommonPairIntensity t j - (2 / Real.pi)| ≤
        56 * (2 / Real.pi) / sourceCommonPairInnerRadius t j := by
  obtain ⟨Jmin, hobs⟩ := source_early_common_observation
  refine ⟨Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, hg⟩ := hobs J₀ hJ₀
  obtain ⟨a₁, hl⟩ := source_early_distance_levels J₀
  refine ⟨max a₀ a₁, ha₀.trans (le_max_left _ _), ?_⟩
  filter_upwards [hg, hl, source_early_common_intensity] with t hg hl hi
  intro b w hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let j := a - sourceEarlyDistanceGap a J₀
  have hν := (hl a ((le_max_right _ _).trans ha) hrange).2.2
  have hj : j ≤ 2 * sourceCoarseLowerLevel t := by dsimp [j]; omega
  obtain ⟨_, _, _, hKD, hcap⟩ := hg b w hbw ((le_max_left _ _).trans ha) hrange
  have hα := hi j hj
  have hc := hcap.trans (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  exact ⟨referenceMarkLaw_isProbabilityMeasure _ _ _ hα.2.1.le hc,
    fun z ↦ referenceMark_mean _ _ hKD _ hα.2.1.le hc z, hα.2.2.2⟩

end SRWTightness
