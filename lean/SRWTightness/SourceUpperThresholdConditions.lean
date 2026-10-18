import SRWTightness.SourceUpperDepthLogLimit
import SRWTightness.SourceUpperFineRatioLimit
import SRWTightness.SourceUpperUniformThreshold

open Filter
open scoped Topology
namespace SRWTightness

/-- All deterministic scale conditions in the uniform threshold bound hold eventually. -/
theorem source_upper_threshold_conditions (hScale : ExponentialFloorScaleInput) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ t : ℝ in atTop,
      0 < t ∧ 1 ≤ Real.log t ∧ 5 * sourceUpperBuffer t ≤ sourceUpperRadius t ∧
      t / 2 ≤ sourceUpperTotalDepth t ∧ |sourceUpperTotalDepth t - t| ≤ B ∧
      1 ≤ upperTerminalFineRadius (sourceUpperLogRadius t) ∧
      1 ≤ upperTerminalDepth (sourceUpperLogRadius t) ∧
      upperTerminalDepth (sourceUpperLogRadius t) ≤ t := by
  let B := diskGreenEnergyConstant / (2 / Real.pi) + Real.log 32 + 4
  have hB : 0 ≤ B := by
    have hl : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
    have hg := diskGreenEnergyConstant_pos
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  obtain ⟨u₀, _, hs⟩ := hScale 4 (by norm_num)
  obtain ⟨v₀, _, hv⟩ := source_upper_terminal_scale_conditions hScale 1 1
    (by norm_num) (by norm_num)
  have hsmall := (source_upper_depth_log_power_limit hScale 0).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [sourceUpperLogRadius_eventually u₀, sourceUpperLogRadius_eventually v₀,
    source_upper_total_depth_eventually hScale, hsmall,
    eventually_ge_atTop (max (Real.exp 1) (2 * B))] with t hu hv' htotal hsmall ht
  have htExp := (le_max_left _ _).trans ht
  have htB := (le_max_right _ _).trans ht
  have ht0 : 0 < t := (Real.exp_pos _).trans_le htExp
  have hlog := Real.log_le_log (Real.exp_pos 1) htExp
  rw [Real.log_exp] at hlog
  obtain ⟨_, hr, _, hsep, _, _⟩ := hs (sourceUpperLogRadius t) hu
  have hR : upperTerminalRadius (sourceUpperLogRadius t) ≤ 3 * sourceUpperRadius t := by
    unfold upperTerminalRadius sourceUpperRadius
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le
      (Real.exp_pos (sourceUpperLogRadius t)).le]
  have hsize : 5 * sourceUpperBuffer t ≤ sourceUpperRadius t := by
    unfold sourceUpperBuffer
    nlinarith
  have hT : t / 2 ≤ sourceUpperTotalDepth t := by
    have hb := (abs_le.mp htotal).1
    change -B ≤ sourceUpperTotalDepth t - t at hb
    linarith
  have hdlo : 1 ≤ upperTerminalDepth (sourceUpperLogRadius t) :=
    (hv (sourceUpperLogRadius t) hv').2.2.2.1
  simp only [pow_zero, mul_one] at hsmall
  have hdhi : upperTerminalDepth (sourceUpperLogRadius t) ≤ t := by
    have hh := (div_lt_iff₀ ht0).mp hsmall
    linarith
  exact ⟨ht0, hlog, hsize, hT, htotal, hr, hdlo, hdhi⟩

end SRWTightness
