import SRWTightness.SourceContinuationBandIntegral
import SRWTightness.SourceTerminalMarkProbability
import SRWTightness.SourceContinuationRange
import SRWTightness.SourceGWActualLowerTubeProbability

open MeasureTheory Filter
namespace SRWTightness

/-- Remaining natural generation count in the source reference continuation. -/
noncomputable def sourceContinuationLength (t : ℝ) (ν : ℕ) : ℕ := (sourceCoarseGeneration t).toNat - ν

/-- The source reference continuation probability, including the stipulated zero-population case. -/
noncomputable def sourceContinuationProbability (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (ν k : ℕ) : ℝ :=
  if k = 0 then 0 else
    ∫ r in sourceContinuationBand t ν (sourceContinuationLength t ν),
      sourceTerminalMarkProbability t A γ b I z
        (geometricGWPopulation r (sourceContinuationLength t ν))
      ∂geometricGWRecordLaw k (sourceContinuationLength t ν)

/-- The source continuation horizon realizes the untruncated remaining generation count. -/
theorem source_continuation_length_eq :
    ∀ᶠ t : ℝ in atTop, ∀ ν : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
      (ν : ℝ) + (sourceContinuationLength t ν : ℝ) = (sourceCoarseGeneration t : ℝ) := by
  filter_upwards [source_gw_natural_generation, source_continuation_remaining_time,
    eventually_ge_atTop (0 : ℝ)] with t hn ht ht0
  intro ν hν
  have hle : (ν : ℝ) ≤ ((sourceCoarseGeneration t).toNat : ℝ) := by
    rw [hn.1]
    linarith [ht ν hν]
  have hnat : ν ≤ (sourceCoarseGeneration t).toNat := by exact_mod_cast hle
  unfold sourceContinuationLength
  rw [Nat.cast_sub hnat, hn.1]
  ring

end SRWTightness
