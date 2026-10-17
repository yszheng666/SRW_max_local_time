import SRWTightness.SourceContinuationRange

open Filter
namespace SRWTightness

/-- The actual early-generation cutoff is the literal original-radius ceiling of source (7.29). -/
theorem source_early_cutoff_at_radius (R : ℝ) :
    sourceCoarseLowerLevel (Real.log R) =
      Nat.ceil ((1000 * Real.log (Real.log R)) ^ (5 / 2 : ℝ)) := rfl

/-- The integer cutoff retains the exact one-unit rounding interval. -/
theorem source_early_cutoff_rounding (t : ℝ) (ht : 0 ≤ Real.log t) :
    (1000 * Real.log t) ^ (5 / 2 : ℝ) ≤ (sourceCoarseLowerLevel t : ℝ) ∧
      (sourceCoarseLowerLevel t : ℝ) < (1000 * Real.log t) ^ (5 / 2 : ℝ) + 1 := by
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩

/-- All early continuations retain their terminal reserve at sufficiently large real radii. -/
theorem source_early_cutoff_original_reserve :
    ∀ᶠ R : ℝ in atTop, 2 * (sourceCoarseLowerLevel (Real.log R) : ℝ) ≤
      sourceLowerTime (sourceLowerRadius (Real.log R)) :=
  Real.tendsto_log_atTop.eventually source_continuation_cutoff_reserve

end SRWTightness
