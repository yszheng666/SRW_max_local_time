import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

open Filter
open scoped Topology

namespace SRWTightness

/-- Every fixed affine logarithmic error is eventually smaller than a positive power budget. -/
theorem affine_log_eventually_le_rpow (A B c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, A * Real.log x + B ≤ c * x ^ γ := by
  have hl : Tendsto (fun x : ℝ ↦ Real.log x / x ^ γ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hγ).tendsto_div_nhds_zero
  have hb : Tendsto (fun x : ℝ ↦ B / x ^ γ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hγ)
  have hh : Tendsto (fun x : ℝ ↦ A * (Real.log x / x ^ γ) + B / x ^ γ)
      atTop (𝓝 0) := by simpa using (hl.const_mul A).add hb
  filter_upwards [(tendsto_order.1 hh).2 c hc, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have he : (A * Real.log x + B) / x ^ γ =
      A * (Real.log x / x ^ γ) + B / x ^ γ := by rw [add_div, mul_div_assoc]
  rw [← he] at hx
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hx0 γ)).mp hx).le

end SRWTightness
