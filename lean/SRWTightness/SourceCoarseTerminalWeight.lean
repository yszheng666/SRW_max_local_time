import SRWTightness.CoarseTerminalWeight
import SRWTightness.SourceGWActualLowerTubeProbability

open Filter
open scoped Topology

namespace SRWTightness

/-- The product of actual coarse and terminal weights has the uniform one-point scale. -/
theorem source_coarse_terminal_weight :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      let L := (sourceCoarseGeneration t).toNat
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        let d := sourceLowerTime (sourceLowerRadius t)
        let w := ((1 + q) / (L : ℝ) ^ 2 *
          Real.exp (-(sourceTerminalRoot t q ^ 2 / (2 * (L : ℝ))))) *
            (Real.exp (-2 * d - 2 * q) / d)
        c * (Real.exp (-2 * t) * (1 + q) / d) ≤ w ∧
          w ≤ C * (Real.exp (-2 * t) * (1 + q) / d) := by
  obtain ⟨K, hK, hmain⟩ := source_coarse_exponent_expansion
  refine ⟨Real.exp (-K - 1) / 4, 16 * Real.exp (K + 1), by positivity, by positivity, ?_⟩
  have herr := (tendsto_order.1 source_coarse_terminal_error_tendsto_zero).2 1 (by norm_num)
  filter_upwards [hmain, source_coarse_terminal_error_uniform, herr,
    source_deficit_large_conditions, source_gw_natural_generation] with t hm hu he ht hNat
  obtain ⟨ht, htE, hdsmall, hlog⟩ := ht
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hd := sourceLowerTime_ge_one t ht
  have hT := sourceTotalTime_ge_half t ht htE
  have hTerr := (abs_le.mp (sourceTotalTime_error t ht)).2
  unfold sourceTotalTime at hT hTerr
  have hNl : t / 4 ≤ (sourceCoarseGeneration t : ℝ) := by linarith
  have hNu : (sourceCoarseGeneration t : ℝ) ≤ 2 * t := by linarith
  dsimp only
  intro q hql hqu
  rw [hNat.1]
  have hh := coarse_terminal_weight_bounds t (sourceLowerTime (sourceLowerRadius t))
    (sourceCoarseGeneration t : ℝ) q K
    ((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) ^ 2 /
      (2 * (sourceCoarseGeneration t : ℝ)))
    ((sourceBarrierSlope t - 2) * q - q ^ 2 / (2 * (sourceCoarseGeneration t : ℝ)))
    (by linarith) (by linarith) ((Real.sqrt_nonneg _).trans hql) hNl hNu hm
    ((hu.2 q hql hqu).trans he.le)
  rw [← source_coarse_terminal_exponential t q hu.1.ne'] at hh
  simpa only [mul_div_assoc, mul_assoc] using hh

end SRWTightness
