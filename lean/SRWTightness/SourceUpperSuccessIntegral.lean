import SRWTightness.SourceUpperSuccessProbability
import SRWTightness.SourceUpperForestJointProbability

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Actual fixed-root block success is bounded by the terminal marked-GW integral. -/
theorem source_upper_success_integral_bound (hinput : PotentialKernelAsymptoticInput)
    (hScale : ExponentialFloorScaleInput) :
    ∃ B W L : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 1 ≤ L ∧ ∀ᶠ t : ℝ in atTop,
      ∀ b ∈ sourceUpperBlockCenters t,
      ∀ [MeasurableSpace (List (Mark (sourceUpperBlock t b)))]
        [MeasurableSingletonClass (List (Mark (sourceUpperBlock t b)))],
      MarkedGWForestJointInput (Mark (sourceUpperBlock t b)) →
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
          ∫⁻ g in sourceUpperGWBand t s (sourceUpperBlockRoot t b)
              (sourceUpperBlockForestDepth t b),
            independentForestLaw (sourceUpperBlockMarkLaw t b)
              (geometricGWPopulation g (sourceUpperBlockForestDepth t b))
              (sourceUpperMarkListHighEvent t s b)
            ∂geometricGWRecordLaw j (sourceUpperBlockForestDepth t b) := by
  obtain ⟨B, W, L, hB, hW, hL, hh⟩ := source_upper_success_probability hinput hScale
  refine ⟨B, W, L, hB, hW, hL, ?_⟩
  filter_upwards [hh, source_upper_forest_joint_probability] with t ht hjoint
  intro b hb inst₁ inst₂ hmarked inst₃ inst₄ inst₅ inst₆ s hs hslog j hj hjcap
  have hprob := ht b hb (markedGWJoint_population hmarked.singleRoot) s hs hslog j hj hjcap
  have hmono := measure_mono (μ := independentForestLaw
    (finiteRecordReferenceMeasure (sourceUpperBlockMarkLaw t b)
      (sourceUpperBlockForestDepth t b)) j)
    (show {rs | rs.length = j ∧ rs ∈ sourceUpperForestSuccess t s b} ⊆
      sourceUpperForestSuccess t s b from fun _ h ↦ h.2)
  rw [hjoint b hb hmarked s j] at hmono
  exact hprob.trans (mul_le_mul_left' hmono _)

end SRWTightness
