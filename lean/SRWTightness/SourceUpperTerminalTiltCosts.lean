import SRWTightness.SourceUpperTerminalTiltUniform
import SRWTightness.SourceUpperTerminalSqrtScale

open Filter

namespace SRWTightness

/-- Both positive and negative terminal-window tilt costs are uniformly bounded at source scales. -/
theorem source_upper_terminal_tilt_costs (hScale : ExponentialFloorScaleInput)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let β := sourceUpperTarget t s /
        (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) - 2
      let Q := 7 + s + d ^ (1 / 4 : ℝ)
      Real.exp (c / d + 2 * d * β ^ 2 / c) ≤ Real.exp (c + 2 / c) ∧
        Real.exp (|β| * Q) ≤ Real.exp 9 := by
  filter_upwards [source_upper_terminal_sqrt_scale hScale,
    source_upper_terminal_tilt_uniform hScale 1 (by norm_num)] with t ht htilt
  intro b hb s hs hslog
  dsimp only
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let β := sourceUpperTarget t s /
    (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) - 2
  have hsqrt : 1 ≤ Real.sqrt d := ht.1
  have hsqrt0 : 0 < Real.sqrt d := by linarith
  have hd0 : 0 < d := Real.sqrt_pos.mp hsqrt0
  have hsq : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd0.le
  have hd1 : 1 ≤ d := by nlinarith
  have hβ : d * β ^ 2 ≤ 1 := htilt b hb s hs hslog
  have hroot : d ^ (1 / 4 : ℝ) ≤ Real.sqrt d := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
  have hQ : 7 + s + d ^ (1 / 4 : ℝ) ≤ 9 * Real.sqrt d := by linarith [ht.2]
  have hnormsq : (|β| * Real.sqrt d) ^ 2 ≤ 1 := by
    rw [mul_pow, sq_abs, hsq]
    nlinarith
  have hnorm : |β| * Real.sqrt d ≤ 1 := by nlinarith
  constructor
  · apply Real.exp_le_exp.mpr
    have hcd : c / d ≤ c := (div_le_iff₀ hd0).mpr (by nlinarith)
    have hbdiv : 2 * d * β ^ 2 / c ≤ 2 / c :=
      div_le_div_of_nonneg_right (by nlinarith) hc.le
    change c / d + 2 * d * β ^ 2 / c ≤ c + 2 / c
    linarith
  · apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hQ (abs_nonneg β)
    change |β| * (7 + s + d ^ (1 / 4 : ℝ)) ≤ 9
    nlinarith

end SRWTightness
