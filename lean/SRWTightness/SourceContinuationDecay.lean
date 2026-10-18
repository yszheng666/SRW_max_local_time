import SRWTightness.SourceContinuationExponentLower
import SRWTightness.ContinuationDecay

open Filter
namespace SRWTightness

/-- The first continuation majorant reduces uniformly to the source early-generation decay. -/
theorem source_continuation_decay :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in atTop, ∀ (ν : ℕ) (x : ℝ),
      ν ≤ 2 * sourceCoarseLowerLevel t → 0 ≤ x → x ≤ 4 + sourceBarrierSlope t * ν →
      ((ν : ℝ) + 1) * Real.sqrt x / t ^ 2 *
        Real.exp (-2 * sourceLowerTime (sourceLowerRadius t)) *
        Real.exp (-((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - x) ^ 2 /
          (2 * ((sourceCoarseGeneration t : ℝ) - ν)))) ≤
      K * ((ν : ℝ) + 1) ^ (3 / 2 : ℝ) * Real.exp (-2 * t - 2 * ν + 2 * x) := by
  obtain ⟨C, hC, hc⟩ := source_continuation_exponent_lower
  refine ⟨2 * Real.exp C, by positivity, ?_⟩
  filter_upwards [hc, source_deficit_large_conditions] with t hc ht
  intro ν x hν hx hxA
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  have hexp := continuation_exponential_decay t (sourceLowerTime (sourceLowerRadius t))
    (ν : ℝ) x
    ((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - x) ^ 2 /
      (2 * ((sourceCoarseGeneration t : ℝ) - ν))) C (by linarith) (hc ν x hν hx)
  have hpre := continuation_initial_prefactor (ν : ℝ) (sourceBarrierSlope t) x
    (Nat.cast_nonneg _) (sourceBarrierSlope_bounds t ht.1 ht.2.1).2 hxA
  have hh := mul_le_mul hpre hexp (by positivity) (by positivity :
    0 ≤ 2 * ((ν : ℝ) + 1) ^ (3 / 2 : ℝ))
  calc
    _ = (((ν : ℝ) + 1) * Real.sqrt x) *
        (Real.exp (-2 * sourceLowerTime (sourceLowerRadius t)) *
          Real.exp (-((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - x) ^ 2 /
            (2 * ((sourceCoarseGeneration t : ℝ) - ν)))) / t ^ 2) := by ring
    _ ≤ (2 * ((ν : ℝ) + 1) ^ (3 / 2 : ℝ)) *
        (Real.exp C * Real.exp (-2 * t - 2 * ν + 2 * x)) := hh
    _ = _ := by ring

end SRWTightness
