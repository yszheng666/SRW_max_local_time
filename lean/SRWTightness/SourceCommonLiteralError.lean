import SRWTightness.SourceCommonGapExponential
import SRWTightness.SourceForestErrorDecay

open Filter
open scoped Topology

namespace SRWTightness

/-- The exact deterministic comparison-error expression displayed at the common endpoint. -/
noncomputable def sourceCommonLiteralError (C t : ℝ) (j : ℕ) : ℝ :=
  C * t ^ 2 * (14 / sourceCommonPairInnerRadius t j +
    ((sourceCommonPairGap t : ℝ) + 1) * Real.exp (-(sourceCommonPairGap t : ℝ)))

/-- A single majorant controls every coarse level, including the last coarse level. -/
theorem source_common_literal_error_majorant (C t : ℝ) (j : ℕ) (hC : 0 ≤ C)
    (ht : 1 ≤ t) (hj : j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t)) :
    sourceCommonLiteralError C t j ≤
      C * (14 * Real.exp 1 * t ^ 2 / sourceLowerRadius t +
        (10 * Real.log t + 7) / t ^ 8) := by
  have hi : 14 / sourceCommonPairInnerRadius t j ≤
      14 * Real.exp 1 / sourceLowerRadius t := by
    calc
      _ ≤ 14 / (sourceLowerRadius t / Real.exp 1) :=
        div_le_div_of_nonneg_left (by norm_num)
          (div_pos (sourceLowerRadius_pos t) (Real.exp_pos 1))
          (source_common_inner_radius_full_range t j hj)
      _ = _ := by field_simp
  have hf := mul_le_mul_of_nonneg_left hi (sq_nonneg t)
  have hg := source_common_gap_error_majorant t ht
  unfold sourceCommonLiteralError
  calc
    _ = C * (t ^ 2 * (14 / sourceCommonPairInnerRadius t j) +
        t ^ 2 * (((sourceCommonPairGap t : ℝ) + 1) *
          Real.exp (-(sourceCommonPairGap t : ℝ)))) := by ring
    _ ≤ C * (t ^ 2 * (14 * Real.exp 1 / sourceLowerRadius t) +
        (10 * Real.log t + 7) / t ^ 8) :=
      mul_le_mul_of_nonneg_left (add_le_add hf hg) hC
    _ = _ := by ring

/-- The literal common-endpoint error majorant tends to zero. -/
theorem source_common_literal_majorant_tendsto_zero (C : ℝ) :
    Tendsto (fun t : ℝ ↦ C * (14 * Real.exp 1 * t ^ 2 / sourceLowerRadius t +
      (10 * Real.log t + 7) / t ^ 8)) atTop (𝓝 0) := by
  have hf : Tendsto (fun t : ℝ ↦ 14 * Real.exp 1 * t ^ 2 / sourceLowerRadius t)
      atTop (𝓝 0) := by
    have h := (source_forest_quadratic_error_tendsto_zero 1 0 1).const_mul
      (14 * Real.exp 1 / 224)
    have he : (fun t : ℝ ↦ 14 * Real.exp 1 * t ^ 2 / sourceLowerRadius t) =
        fun t ↦ (14 * Real.exp 1 / 224) * sourceForestQuadraticError 1 0 1 t := by
      funext t
      unfold sourceForestQuadraticError
      ring
    rw [he]
    simpa using h
  have hl : Tendsto (fun t : ℝ ↦ Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h7 : Tendsto (fun t : ℝ ↦ 1 / t ^ 7) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (7 : ℕ) ≠ 0))
  have h8 : Tendsto (fun t : ℝ ↦ 1 / t ^ 8) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (8 : ℕ) ≠ 0))
  have hg : Tendsto (fun t : ℝ ↦ (10 * Real.log t + 7) / t ^ 8) atTop (𝓝 0) := by
    have h := ((hl.mul h7).const_mul 10).add (h8.const_mul 7)
    have he : (fun t : ℝ ↦ (10 * Real.log t + 7) / t ^ 8) =
        fun t ↦ 10 * ((Real.log t / t) * (1 / t ^ 7)) + 7 * (1 / t ^ 8) := by
      funext t
      by_cases ht : t = 0
      · simp [ht]
      · field_simp
        <;> ring
    rw [he]
    simpa using h
  simpa using (hf.add hg).const_mul C

/-- The literal source error is uniformly o(1) over the complete coarse endpoint range. -/
theorem source_common_literal_error_uniform (C : ℝ) (hC : 0 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ,
      j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      |sourceCommonLiteralError C t j| < ε := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (source_common_literal_majorant_tendsto_zero C).eventually (gt_mem_nhds hε)]
      with t ht he
  intro j hj
  have hn : 0 ≤ sourceCommonLiteralError C t j := by
    unfold sourceCommonLiteralError
    have hm := (sourceCommonPairInnerRadius_pos t j).le
    positivity
  rw [abs_of_nonneg hn]
  exact (source_common_literal_error_majorant C t j hC ht hj).trans_lt he

end SRWTightness
