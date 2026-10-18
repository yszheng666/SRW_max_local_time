import SRWTightness.SourceEarlyRootPairMean
import SRWTightness.SourceEarlyCapacityDenominator
import SRWTightness.RootMeanPerturbation

open MeasureTheory Filter
namespace SRWTightness

/-- Equation 8.16 with explicit inverse-radius errors and leading coefficient two. -/
theorem source_early_root_pair_mean_error (hLast : FiniteLastVisitCountInput)
    (hinput : PotentialKernelAsymptoticInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      |(∫ Y, ((sourceCommonWordRootCount t b ν Y +
        sourceCommonWordRootCount t w ν Y : ℕ) : ℝ) ∂sourceCommonWordLaw t b w j) - 2| ≤
        224 / sourceCommonPairInnerRadius t j + C / sourceCommonPairInnerRadius t ν := by
  obtain ⟨D, hD, hc⟩ := source_early_capacity_denominator hinput
  obtain ⟨Jmin, hp⟩ := source_early_root_pair_mean hLast
  let g : ℝ := 2 / Real.pi
  have hg : 0 < g := by dsimp [g]; positivity
  refine ⟨4 * D / g, by positivity, Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, hm⟩ := hp J₀ hJ₀
  obtain ⟨a₁, hl⟩ := source_early_distance_levels J₀
  refine ⟨max a₀ a₁, ha₀.trans (le_max_left _ _), ?_⟩
  filter_upwards [hm, hl, hc, source_early_common_intensity] with t hm hl hc hi
  intro b w hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  have hν := (hl a ((le_max_right _ _).trans ha) hrange).2.2
  have hj : j ≤ 2 * sourceCoarseLowerLevel t := by dsimp [j]; omega
  have hmean := hm b w hbw ((le_max_left _ _).trans ha) hrange
  obtain ⟨d, hd, herr, hcap⟩ := hc ν hν b
  rw [hmean, hcap]
  have hh := root_pair_mean_ratio_error g (sourceCommonPairIntensity t j) d d
    (56 * g / sourceCommonPairInnerRadius t j)
    (D / sourceCommonPairInnerRadius t ν) (D / sourceCommonPairInnerRadius t ν)
    hg hd hd (hi j hj).2.2.2 herr herr
  calc
    _ = |sourceCommonPairIntensity t j * (d⁻¹ + d⁻¹) - 2| := by congr 1; ring
    _ ≤ _ := hh
    _ = _ := by field_simp <;> ring

end SRWTightness
