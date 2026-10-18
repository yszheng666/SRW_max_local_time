import SRWTightness.SourceCommonLiteralForestError
import SRWTightness.SourceCommonPrefixPopulationCap
import SRWTightness.SourceCommonSignedLevel

open Filter

namespace SRWTightness

/-- The actual common-prefix error is bounded by the original expression, uniformly o(1). -/
theorem source_common_prefix_literal_error (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ρ : ℝ) (j : ℕ), 1 ≤ ρ →
      ρ ≤ sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 →
      (j : ℤ) = sourceSignedCommonPairLevel t ρ →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (M : Type) (r : FiniteExcursionRecord M j),
      (∀ k : ℕ, 0 < k → k ≤ j →
        geometricGWHeight (finiteRecordPopulationList j r) k ≤
          4 + sourceBarrierSlope t * k -
            (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ)) →
      finiteRecordError
        (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceCommonPairInnerRadius t j) i))
        (fun _ ↦ 2 * (W * (2 * ρ + 1) / sourceCommonPairInnerRadius t j *
          Real.log (sourceCommonPairInnerRadius t j / (2 * ρ)))) j r ≤
        sourceCommonLiteralError (128 * B + 48 * Real.exp 1 * W) t j ∧
      |sourceCommonLiteralError (128 * B + 48 * Real.exp 1 * W) t j| < ε := by
  have hC : 0 ≤ 128 * B + 48 * Real.exp 1 * W := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ), source_common_prefix_population_cap,
    source_common_literal_error_uniform _ hC ε hε] with t ht hp he
  intro ρ j hρ houter hj hdepth M r hbar
  have hi := source_common_signed_level_index_sum t ρ ht j hj
  have hpop := hp j hdepth M r hbar
  have hb := source_common_forest_literal_error B W 8 t ρ j hB hW (by norm_num)
    ht hρ houter hi j [r] (by
      intro i hi
      simpa only [forestLevelPopulation, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero] using hpop i hi)
  have hconst : 16 * B * 8 + 6 * Real.exp 1 * W * 8 =
      128 * B + 48 * Real.exp 1 * W := by ring
  rw [hconst] at hb
  constructor
  · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using hb
  · exact he j (by omega)

end SRWTightness
