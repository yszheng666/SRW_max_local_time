import SRWTightness.SourceContinuationProbability
import SRWTightness.SourceContinuationWindowIntegral

open MeasureTheory
namespace SRWTightness

/-- The actual continuation weight is a probability, including the zero-population convention. -/
theorem source_continuation_probability_mem (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (ν k : ℕ)
    (hα : 0 ≤ sourceReferenceIntensity (sourceLowerRadius t) 14)
    (hcap : sourceReferenceIntensity (sourceLowerRadius t) 14 *
      capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ≤ 1) :
    sourceContinuationProbability t A γ b I z ν k ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hk : k = 0
  · simp [sourceContinuationProbability, hk]
  · rw [sourceContinuationProbability, if_neg hk]
    let L := sourceContinuationLength t ν
    let P := fun r : GeometricGWRecord ↦ sourceTerminalMarkProbability t A γ b I z
      (geometricGWPopulation r L)
    let S := sourceContinuationBand t ν L
    have hP (r : GeometricGWRecord) : P r ∈ Set.Icc (0 : ℝ) 1 :=
      source_terminal_mark_probability_mem t A γ b I z _ hα hcap
    have hi := gw_forest_probability_integrable k L P hP
    refine ⟨integral_nonneg (fun r ↦ (hP r).1), ?_⟩
    calc
      (∫ r in S, P r ∂geometricGWRecordLaw k L) ≤
          ∫ _ in S, (1 : ℝ) ∂geometricGWRecordLaw k L :=
        setIntegral_mono_on hi.integrableOn (integrable_const 1).integrableOn
          S.to_countable.measurableSet (fun r _ ↦ (hP r).2)
      _ = (geometricGWRecordLaw k L).real S := by simp
      _ ≤ 1 := measureReal_le_one

end SRWTightness
