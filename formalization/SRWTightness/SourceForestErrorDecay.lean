import SRWTightness.SourceForestQuadraticError
import SRWTightness.SourceTerminalThresholdUniform

open Filter
open scoped Topology

namespace SRWTightness

/-- The deterministic source error bound under quadratic generation caps. -/
noncomputable def sourceForestQuadraticError (B W D t : ℝ) : ℝ :=
  224 * B * D * t ^ 2 / sourceLowerRadius t + 24 * W * D * Real.log t / t ^ 4

/-- The full count-controlled comparison error vanishes on the actual source radius profile. -/
theorem source_forest_quadratic_error_tendsto_zero (B W D : ℝ) :
    Tendsto (sourceForestQuadraticError B W D) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun t : ℝ ↦ t ^ 2 / sourceLowerRadius t) atTop (𝓝 0) := by
    have hmajor : Tendsto (fun t : ℝ ↦ 1 / t ^ 5) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0))
    apply squeeze_zero' _ _ hmajor
    · filter_upwards [] with t
      exact div_nonneg (sq_nonneg t) (sourceLowerRadius_pos t).le
    · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
      have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
      have ht0 : 0 < t := by linarith
      have hh := div_le_div_of_nonneg_left (sq_nonneg t) (pow_pos ht0 7)
        (sourceLowerRadius_ge_seventh_power t ht)
      exact hh.trans_eq (by field_simp)
  have hlog : Tendsto (fun t : ℝ ↦ Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Tendsto (fun t : ℝ ↦ 1 / t ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0))
  have hsecond : Tendsto (fun t : ℝ ↦ Real.log t / t ^ 4) atTop (𝓝 0) := by
    have heq : (fun t : ℝ ↦ Real.log t / t ^ 4) =
        (fun t : ℝ ↦ (Real.log t / t) * (1 / t ^ 3)) := by
      funext t
      by_cases ht : t = 0
      · simp [ht]
      · field_simp <;> ring
    rw [heq]
    simpa using hlog.mul hinv
  have hh := (hfirst.const_mul (224 * B * D)).add (hsecond.const_mul (24 * W * D))
  have heq : sourceForestQuadraticError B W D = fun t : ℝ ↦
      (224 * B * D) * (t ^ 2 / sourceLowerRadius t) +
        (24 * W * D) * (Real.log t / t ^ 4) := by
    funext t
    unfold sourceForestQuadraticError
    ring
  rw [heq]
  simpa only [mul_zero, add_zero] using hh

end SRWTightness
