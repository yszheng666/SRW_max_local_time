import SRWTightness.MarkSumGenerating

namespace SRWTightness

/-- A constant occupation weight is the exponential of total occupation. -/
theorem markMonomial_constant_exp (A : Finset Site) (v : ℝ) (hv : 0 < v) (Y : Mark A) :
    markMonomial (fun _ : A ↦ v) Y =
      Real.exp ((∑ z : A, (Y z : ℝ)) * Real.log v) := by
  have hp (z : A) : v ^ Y z = Real.exp ((Y z : ℝ) * Real.log v) := by
    rw [Real.exp_nat_mul, Real.exp_log hv]
  unfold markMonomial
  simp_rw [hp]
  rw [← Real.exp_sum, ← Finset.sum_mul]

end SRWTightness
