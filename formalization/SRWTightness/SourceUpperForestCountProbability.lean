import SRWTightness.SourceUpperForestProbability

open Filter MeasureTheory
open scoped ENNReal Topology

namespace SRWTightness

/-- Generation caps give the actual upper forest probability bound with its vanishing error. -/
theorem source_upper_forest_count_probability (hinput : PotentialKernelAsymptoticInput) :
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
      ∀ j : ℕ, 1 ≤ j →
      ∀ s : Set (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
        (sourceUpperBlockForestDepth t b))),
      (∀ rs ∈ s, rs.length = j) →
      (∀ rs ∈ s, ∀ i ≤ sourceUpperBlockForestDepth t b,
        (forestLevelPopulation (sourceUpperBlockForestDepth t b) rs i : ℝ) ≤ 16 * t ^ 2) →
      pathLaw {ω | sourceUpperBlockForest t b (wordOccupationMark (sourceUpperBlock t b)) ω ∈ s} ≤
        ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + L)) ^ (j - 1) *
          Real.exp ((3584 * B + 96 * W) * t ^ 2 * sourceUpperLogRadius t *
            Real.exp (-3 * sourceUpperLogRadius t / 4))) *
          independentForestLaw
            (finiteRecordReferenceMeasure (sourceUpperBlockMarkLaw t b)
              (sourceUpperBlockForestDepth t b)) j s := by
  obtain ⟨B, W, L, hB, hW, hL, hh⟩ := source_upper_forest_probability hinput
  refine ⟨B, W, L, hB, hW, hL, ?_⟩
  filter_upwards [hh, source_upper_forest_error_bound B W hB hW] with t ht he
  intro b hb hmarked inst₁ inst₂ inst₃ inst₄ j hj s hlen hcounts
  apply ht b hb hmarked j hj s _ hlen
  intro rs hrs
  have hr : (1 : ℝ) ≤ upperTerminalFineRadius (sourceUpperLogRadius t) := by
    change (1 : ℝ) ≤ (sourceUpperBlockSide t : ℝ)
    exact_mod_cast (show 1 ≤ sourceUpperBlockSide t from sourceUpperBlockSide_pos t)
  exact he (2 * upperTerminalFineRadius (sourceUpperLogRadius t)) (by linarith) le_rfl
    (Mark (sourceUpperBlock t b)) (sourceUpperBlockForestDepth t b) rs (hcounts rs hrs)

/-- The uniform multiplicative error in the actual forest comparison tends to one. -/
theorem source_upper_forest_comparison_factor_tendsto_one (B W : ℝ) :
    Tendsto (fun t : ℝ ↦ Real.exp ((3584 * B + 96 * W) * t ^ 2 * sourceUpperLogRadius t *
      Real.exp (-3 * sourceUpperLogRadius t / 4))) atTop (𝓝 1) := by
  simpa only [Real.exp_zero, Function.comp_def] using (Real.continuous_exp.tendsto 0).comp
    (source_upper_actual_forest_error_majorant_vanishes B W)

end SRWTightness
