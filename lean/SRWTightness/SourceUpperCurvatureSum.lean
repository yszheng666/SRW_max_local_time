import SRWTightness.BarrierCurvatureSum
import SRWTightness.SourceUpperBarrierDefinition

open Filter

namespace SRWTightness

/-- The actual terminal curvature eventually dominates four logarithms of the outer scale. -/
theorem source_upper_terminal_curvature_lower (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop,
      4 * Real.log t ≤ upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) := by
  let B := diskGreenEnergyConstant / (2 / Real.pi) + 2
  filter_upwards [source_upper_terminal_depth_eventually hScale,
    eventually_ge_atTop (Real.exp (max 1 B))] with t hd ht
  have ht0 : 0 < t := (Real.exp_pos _).trans_le ht
  have hl := Real.log_le_log (Real.exp_pos _) ht
  rw [Real.log_exp] at hl
  have hl1 : 1 ≤ Real.log t := (le_max_left _ _).trans hl
  have hlB : B ≤ Real.log t := (le_max_right _ _).trans hl
  have hp : Real.log t ≤ (Real.log t) ^ 4 := le_self_pow₀ hl1 (by norm_num)
  have hb := (abs_le.mp hd).1
  change -B ≤ upperTerminalDepth (sourceUpperLogRadius t) - (8 * Real.log t) ^ 4 at hb
  have hfour : (4 * Real.log t) ^ 4 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
    nlinarith [pow_nonneg (show 0 ≤ Real.log t by linarith) 4]
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ (4 * Real.log t) ^ 4)
    hfour (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [← Real.rpow_natCast_mul (by linarith : 0 ≤ 4 * Real.log t)] at hr
  norm_num at hr
  exact hr

/-- The terminal remainder in the finite barrier sum is uniformly bounded at the source scale. -/
theorem source_upper_curvature_remainder (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop,
      ((sourceUpperCoarseDepth t : ℝ) + 1) ^ 4 *
        Real.exp (-(3 / 2 : ℝ) *
          upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤ 16 := by
  obtain ⟨B, hB, hcond⟩ := source_upper_threshold_conditions hScale
  filter_upwards [hcond, source_upper_terminal_curvature_lower hScale,
    eventually_ge_atTop B] with t ht hr htB
  have ht0 := ht.1
  have hl := ht.2.1
  have htotal := (abs_le.mp ht.2.2.2.2.1).2
  have hd := ht.2.2.2.2.2.2.1
  have hN : (sourceUpperCoarseDepth t : ℝ) + 1 ≤ 2 * t := by
    unfold sourceUpperTotalDepth at htotal
    linarith
  have he : Real.exp (-(3 / 2 : ℝ) *
      upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤ (t ^ 4)⁻¹ := by
    calc
      _ ≤ Real.exp (-(4 * Real.log t)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        have hlog : Real.log (t ^ 4) = 4 * Real.log t := by
          simpa only [Nat.cast_ofNat] using Real.log_pow t 4
        rw [← hlog, Real.exp_neg, Real.exp_log (pow_pos ht0 4)]
  have hp : ((sourceUpperCoarseDepth t : ℝ) + 1) ^ 4 ≤ (2 * t) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hN 4
  calc
    _ ≤ (2 * t) ^ 4 * (t ^ 4)⁻¹ := mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ = 16 := by field_simp; ring

/-- Uniform summability of the exact source barrier curvature over every coarse level. -/
theorem source_upper_curvature_sum (hScale : ExponentialFloorScaleInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      (∑ j ∈ Finset.range (sourceUpperCoarseDepth t + 1), ((j : ℝ) + 1) ^ 3 *
        Real.exp (-(3 / 2 : ℝ) * sourceUpperBarrierCurvature t j)) ≤ C := by
  let S := ∑' j : ℕ, ((j : ℝ) + 1) ^ 3 * Real.exp (-(3 / 2 : ℝ) * (j : ℝ) ^ (1 / 4 : ℝ))
  have hS : 0 ≤ S := tsum_nonneg (fun _ ↦ by positivity)
  refine ⟨S + 16, by linarith, ?_⟩
  obtain ⟨B, _, hcond⟩ := source_upper_threshold_conditions hScale
  filter_upwards [hcond, source_upper_curvature_remainder hScale] with t ht hr
  have hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
    have h := ht.2.2.2.2.2.2.1
    linarith
  have h := barrier_curvature_sum_bound (sourceUpperCoarseDepth t) 3
    (upperTerminalDepth (sourceUpperLogRadius t)) (3 / 2) (1 / 4) hd
    (by norm_num) (by norm_num)
  change (∑ j ∈ Finset.range (sourceUpperCoarseDepth t + 1), ((j : ℝ) + 1) ^ 3 *
    Real.exp (-(3 / 2 : ℝ) * sourceUpperBarrierCurvature t j)) ≤ S + _ at h
  linarith

end SRWTightness
