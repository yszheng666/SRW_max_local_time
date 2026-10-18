import SRWTightness.SourceUpperTerminalSqrtScale

open Filter

namespace SRWTightness

/-- The polynomial prefactor in (4.32) is uniformly bounded at the actual source scales. -/
theorem source_upper_terminal_prefactor (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let Q := 7 + s + d ^ (1 / 4 : ℝ)
      let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
      1 + S / Real.sqrt d + (Q + 1) * S / d ≤ 122 := by
  filter_upwards [source_upper_terminal_sqrt_scale hScale] with t ht
  intro s hs hslog
  dsimp only
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  have hsqrt : 1 ≤ Real.sqrt d := ht.1
  have hlog : Real.log t ≤ Real.sqrt d := ht.2
  have hsqrt0 : 0 < Real.sqrt d := by linarith
  have hd0 : 0 < d := Real.sqrt_pos.mp hsqrt0
  have hsq : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd0.le
  have hd1 : 1 ≤ d := by nlinarith
  have hroot : d ^ (1 / 4 : ℝ) ≤ Real.sqrt d := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
  have hr0 : 0 ≤ d ^ (1 / 4 : ℝ) := Real.rpow_nonneg hd0.le _
  have hS : 8 + s + 2 * d ^ (1 / 4 : ℝ) ≤ 11 * Real.sqrt d := by linarith
  have hQ : 7 + s + d ^ (1 / 4 : ℝ) + 1 ≤ 10 * Real.sqrt d := by linarith
  have hSdiv : (8 + s + 2 * d ^ (1 / 4 : ℝ)) / Real.sqrt d ≤ 11 :=
    (div_le_iff₀ hsqrt0).mpr (by linarith)
  have hprod := mul_le_mul hQ hS (by positivity : 0 ≤ 8 + s + 2 * d ^ (1 / 4 : ℝ))
    (by positivity : 0 ≤ 10 * Real.sqrt d)
  have hproddiv : (7 + s + d ^ (1 / 4 : ℝ) + 1) *
      (8 + s + 2 * d ^ (1 / 4 : ℝ)) / d ≤ 110 := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith
  change 1 + (8 + s + 2 * d ^ (1 / 4 : ℝ)) / Real.sqrt d +
    (7 + s + d ^ (1 / 4 : ℝ) + 1) * (8 + s + 2 * d ^ (1 / 4 : ℝ)) / d ≤ 122
  linarith

end SRWTightness
