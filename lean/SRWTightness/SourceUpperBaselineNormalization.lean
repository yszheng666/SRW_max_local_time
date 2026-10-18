import SRWTightness.SourceUpperBaselineLower
import SRWTightness.SourceUpperBaselineErrorLimit
import SRWTightness.SourceUpperCoarseLinearDepth
import SRWTightness.SourceUpperThresholdConditions

open Filter
open scoped Topology

namespace SRWTightness

/-- A bounded baseline quadratic error uniformly in the actual upper height range. -/
theorem source_upper_baseline_lower_eventually (hScale : ExponentialFloorScaleInput) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      2 * t - 2 * upperTerminalDepth (sourceUpperLogRadius t) - 2 * Real.log t +
        2 * Real.sqrt Real.pi * s - A ≤
          sourceUpperTarget t s ^ 2 / (2 * sourceUpperCoarseDepth t) := by
  obtain ⟨B, hB, hc⟩ := source_upper_threshold_conditions hScale
  refine ⟨2 * B + 1, by positivity, ?_⟩
  filter_upwards [hc, source_upper_coarse_linear_depth,
    (source_upper_baseline_error_limit hScale B).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (max 1 B)] with t ht hN he htB
  intro s hs hslog
  have ht1 : 1 ≤ t := (le_max_left _ _).trans htB
  have hBt : B ≤ t := (le_max_right _ _).trans htB
  have hN0 : (0 : ℝ) < sourceUpperCoarseDepth t := by linarith [hN.1, ht.1]
  have hd0 : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
    linarith [ht.2.2.2.2.2.2.1]
  have hh := source_upper_baseline_lower t s B ht1 hB hBt hs hslog
    ht.2.2.2.1 ht.2.2.2.2.1 hd0 hN0.ne'
  unfold sourceUpperBaselineError at he
  linarith

/-- The baseline exponential and squared depth produce uniform exponential upper-tail decay. -/
theorem source_upper_baseline_exponential (hScale : ExponentialFloorScaleInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      Real.exp (2 * t - 2 * upperTerminalDepth (sourceUpperLogRadius t) -
        sourceUpperTarget t s ^ 2 / (2 * sourceUpperCoarseDepth t)) /
          (sourceUpperCoarseDepth t : ℝ) ^ 2 ≤
        C * Real.exp (-(2 * Real.sqrt Real.pi * s)) := by
  obtain ⟨A, _, ha⟩ := source_upper_baseline_lower_eventually hScale
  refine ⟨4 * Real.exp A, by positivity, ?_⟩
  filter_upwards [ha, source_upper_coarse_linear_depth, eventually_ge_atTop (1 : ℝ)]
    with t ht hN ht1
  intro s hs hslog
  have ht0 : 0 < t := by linarith
  have hN0 : (0 : ℝ) < sourceUpperCoarseDepth t := by linarith [hN.1]
  have hexp := Real.exp_le_exp.mpr (show
      2 * t - 2 * upperTerminalDepth (sourceUpperLogRadius t) -
        sourceUpperTarget t s ^ 2 / (2 * sourceUpperCoarseDepth t) ≤
          2 * Real.log t + A - 2 * Real.sqrt Real.pi * s by
    linarith [ht s hs hslog])
  have hlog : Real.exp (2 * Real.log t) = t ^ 2 := by
    rw [show 2 * Real.log t = Real.log t + Real.log t by ring, Real.exp_add,
      Real.exp_log ht0]
    ring
  have heq : Real.exp (2 * Real.log t + A - 2 * Real.sqrt Real.pi * s) =
      t ^ 2 * Real.exp A * Real.exp (-(2 * Real.sqrt Real.pi * s)) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, hlog]
  rw [heq] at hexp
  have hratio : t ^ 2 / (sourceUpperCoarseDepth t : ℝ) ^ 2 ≤ 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hN0)).mpr
    nlinarith [hN.1]
  calc
    _ ≤ (t ^ 2 * Real.exp A * Real.exp (-(2 * Real.sqrt Real.pi * s))) /
        (sourceUpperCoarseDepth t : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hexp (sq_nonneg _)
    _ = (t ^ 2 / (sourceUpperCoarseDepth t : ℝ) ^ 2) *
        (Real.exp A * Real.exp (-(2 * Real.sqrt Real.pi * s))) := by ring
    _ ≤ 4 * (Real.exp A * Real.exp (-(2 * Real.sqrt Real.pi * s))) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring

end SRWTightness
