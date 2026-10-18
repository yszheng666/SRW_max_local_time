import SRWTightness.SourceContinuationProbability

open MeasureTheory
namespace SRWTightness

/-- The terminal event mass is nonnegative even before reference normalization is invoked. -/
theorem source_terminal_mark_probability_nonneg (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (k : ℕ) :
    0 ≤ sourceTerminalMarkProbability t A γ b I z k := by
  exact measureReal_nonneg

/-- Every original continuation weight is nonnegative, including the stipulated zero-root case. -/
theorem source_continuation_probability_nonneg (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (ν k : ℕ) :
    0 ≤ sourceContinuationProbability t A γ b I z ν k := by
  unfold sourceContinuationProbability
  split_ifs
  · exact le_rfl
  · exact integral_nonneg (fun r ↦ source_terminal_mark_probability_nonneg t A γ b I z _)

end SRWTightness
