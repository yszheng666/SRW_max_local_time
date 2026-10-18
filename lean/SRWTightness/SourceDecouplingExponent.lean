import SRWTightness.SourceForestErrorDecay
import SRWTightness.SourceLongEscapeProbability
import SRWTightness.SourceRootDepth

open Filter
open scoped Topology
namespace SRWTightness

/-- The explicit combined record/count exponent in the certified joint-root comparison. -/
noncomputable def sourceDecouplingExponent (D C B W t : ℝ) (ν J : ℕ) : ℝ :=
  16 * ((ν : ℝ) + 1) ^ 2 *
    (D * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
      C * 15 / (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
    2 * sourceForestQuadraticError B W 8 t

/-- A uniform vanishing remainder for the early return and fine-forest costs. -/
noncomputable def sourceDecouplingSmallError (C B W t : ℝ) : ℝ :=
  1920 * C / t ^ 5 + 2 * sourceForestQuadraticError B W 8 t

/-- The early comparison remainder tends to zero on the exact source scale. -/
theorem source_decoupling_small_error_tendsto_zero (C B W : ℝ) :
    Tendsto (sourceDecouplingSmallError C B W) atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ ↦ 1920 * C / t ^ 5 +
    2 * sourceForestQuadraticError B W 8 t) atTop (𝓝 0)
  have hfirst : Tendsto (fun t : ℝ ↦ 1920 * C / t ^ 5) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0))
  have hsecond := (source_forest_quadratic_error_tendsto_zero B W 8).const_mul 2
  simpa only [mul_zero, add_zero] using hfirst.add hsecond

end SRWTightness
