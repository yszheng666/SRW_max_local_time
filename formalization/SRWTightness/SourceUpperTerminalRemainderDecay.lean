import SRWTightness.SourceUpperTerminalIntegrand
import SRWTightness.SourceUpperTerminalSqrtScale

open Filter
open scoped Topology

namespace SRWTightness

/-- Rounding down the fine radius preserves its squared exponential upper bound. -/
theorem upper_terminal_fine_radius_sq_le (u : ℝ) :
    upperTerminalFineRadius u ^ 2 ≤ Real.exp (u / 2) := by
  have h := Nat.floor_le (Real.exp_nonneg (u / 4))
  change upperTerminalFineRadius u ≤ Real.exp (u / 4) at h
  have h0 : 0 ≤ upperTerminalFineRadius u := by unfold upperTerminalFineRadius; positivity
  calc
    _ ≤ (Real.exp (u / 4)) ^ 2 := by nlinarith [Real.exp_nonneg (u / 4)]
    _ = Real.exp (u / 2) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- The actual terminal remainder beats the exponential spatial counting cost. -/
theorem source_upper_terminal_remainder_decay (hScale : ExponentialFloorScaleInput)
    (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 < ρ) :
    ∀ᶠ t : ℝ in atTop,
      sourceUpperTerminalRemainder t C ρ ≤ C * Real.exp (-5 * t) := by
  have hdlim : Tendsto (fun t : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius t) / t)
      atTop (𝓝 0) := by simpa using source_upper_depth_log_power_limit hScale 0
  have hulim : Tendsto (fun t : ℝ ↦ sourceUpperLogRadius t / t) atTop (𝓝 0) := by
    have hh := (Real.isLittleO_pow_log_id_atTop (n := 4)).tendsto_div_nhds_zero
    convert hh.const_mul (8 ^ 4 : ℝ) using 1 <;> simp [sourceUpperLogRadius, mul_pow, mul_div_assoc]
  filter_upwards [(tendsto_order.1 hdlim).2 (ρ / 6) (by positivity),
    (tendsto_order.1 hulim).2 1 (by norm_num), source_upper_terminal_sqrt_scale hScale,
    eventually_gt_atTop (0 : ℝ)] with t hd hu hsq ht
  have hd0 : 0 < upperTerminalDepth (sourceUpperLogRadius t) :=
    Real.sqrt_pos.mp (by linarith [hsq.1])
  have hdepth : 6 * upperTerminalDepth (sourceUpperLogRadius t) ≤ ρ * t := by
    have := (div_lt_iff₀ ht).mp hd
    linarith
  have hu' : sourceUpperLogRadius t ≤ t := by
    have := (div_lt_iff₀ ht).mp hu
    linarith
  have hcost : 6 * t ≤ ρ * t ^ 2 / upperTerminalDepth (sourceUpperLogRadius t) := by
    apply (le_div_iff₀ hd0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hdepth ht.le]
  calc
    sourceUpperTerminalRemainder t C ρ ≤
        C * Real.exp (sourceUpperLogRadius t / 2) *
          Real.exp (-ρ * t ^ 2 / upperTerminalDepth (sourceUpperLogRadius t)) := by
      unfold sourceUpperTerminalRemainder
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (upper_terminal_fine_radius_sq_le _) hC) (Real.exp_nonneg _)
    _ = C * Real.exp (sourceUpperLogRadius t / 2 -
        ρ * t ^ 2 / upperTerminalDepth (sourceUpperLogRadius t)) := by
      rw [show sourceUpperLogRadius t / 2 -
        ρ * t ^ 2 / upperTerminalDepth (sourceUpperLogRadius t) =
        sourceUpperLogRadius t / 2 +
          (-ρ * t ^ 2 / upperTerminalDepth (sourceUpperLogRadius t)) by ring, Real.exp_add]
      ring
    _ ≤ C * Real.exp (-5 * t) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      linarith

end SRWTightness
