import SRWTightness.SourceUpperSuccessForestCap
import SRWTightness.SourceUpperForestCountProbability

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- A fixed positive root count transfers actual block success to its reference forest. -/
theorem source_upper_success_probability (hinput : PotentialKernelAsymptoticInput)
    (hScale : ExponentialFloorScaleInput) :
    ∃ B W L : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 1 ≤ L ∧ ∀ᶠ t : ℝ in atTop,
      ∀ b ∈ sourceUpperBlockCenters t, MarkedGWTreeInput (Mark (sourceUpperBlock t b)) →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
        (sourceUpperBlockForestDepth t b))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b)))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b)))],
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ t ^ 2 →
      pathLaw {ω | sourceUpperBlockRootCount t b ω = j ∧
        ω ∈ sourceUpperBlockSuccess t s b} ≤
        ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + L)) ^ (j - 1) *
          Real.exp ((3584 * B + 96 * W) * t ^ 2 * sourceUpperLogRadius t *
            Real.exp (-3 * sourceUpperLogRadius t / 4))) *
          independentForestLaw
            (finiteRecordReferenceMeasure (sourceUpperBlockMarkLaw t b)
              (sourceUpperBlockForestDepth t b)) j
            {rs | rs.length = j ∧ rs ∈ sourceUpperForestSuccess t s b} := by
  obtain ⟨B, W, L, hB, hW, hL, hh⟩ := source_upper_forest_count_probability hinput
  refine ⟨B, W, L, hB, hW, hL, ?_⟩
  filter_upwards [hh, source_upper_success_forest_cap hScale,
    source_upper_block_success_iff_ae] with t ht hc he
  intro b hb hmarked inst₁ inst₂ inst₃ inst₄ s hs hslog j hj hjcap
  have heq : pathLaw {ω | sourceUpperBlockRootCount t b ω = j ∧
      ω ∈ sourceUpperBlockSuccess t s b} =
      pathLaw {ω | sourceUpperBlockForest t b (wordOccupationMark (sourceUpperBlock t b)) ω ∈
        {rs | rs.length = j ∧ rs ∈ sourceUpperForestSuccess t s b}} := by
    apply measure_congr
    filter_upwards [he b hb] with ω hω
    apply propext
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [sourceUpperBlockForest_length]
    exact and_congr Iff.rfl (hω s)
  rw [heq]
  apply ht b hb hmarked j hj _ (fun rs hrs ↦ hrs.1)
  intro rs hrs
  apply hc b hb s hs hslog rs hrs.2
  simpa only [hrs.1] using hjcap

end SRWTightness
