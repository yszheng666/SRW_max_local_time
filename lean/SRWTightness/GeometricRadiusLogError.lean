import SRWTightness.LogRadiusPerturbation

namespace SRWTightness

/-- A buffered geometric radius has a logarithmic error uniform over nonnegative levels. -/
theorem geometric_radius_log_error (r ρ H j : ℝ) (hH : 0 < H) (hρ : 4 * H ≤ ρ)
    (hj : 0 ≤ j) (hr : |r - Real.exp j * ρ| ≤ 2 * H) :
    |Real.log r - (Real.log ρ + j)| ≤ 4 * H / ρ := by
  have hρ0 : 0 < ρ := by linarith
  have hj1 : 1 ≤ Real.exp j := Real.one_le_exp_iff.mpr hj
  have hbase : ρ ≤ Real.exp j * ρ := by nlinarith
  have hh := log_radius_perturbation r (Real.exp j * ρ) (2 * H)
    (by linarith) (by linarith) (by linarith [(abs_le.mp hr).1])
    (by linarith [(abs_le.mp hr).2])
  rw [Real.log_mul (Real.exp_pos j).ne' hρ0.ne', Real.log_exp] at hh
  have hd : 4 * H / (Real.exp j * ρ) ≤ 4 * H / ρ :=
    div_le_div_of_nonneg_left (by positivity) hρ0 hbase
  calc
    _ = |Real.log r - (j + Real.log ρ)| := by rw [add_comm (Real.log ρ) j]
    _ ≤ 4 * H / (Real.exp j * ρ) := by convert hh using 1 <;> ring
    _ ≤ _ := hd

end SRWTightness
