import SRWTightness.ExternalKilledTraceFactorization

namespace SRWTightness

/-- Relative numerator and conditioning errors remain relative after division by a rare exit atom. -/
theorem trace_exit_relative_ratio (p h s q ε δ : ℝ) (hh : 0 < h) (hq : 0 < q)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hcond : |h - s| ≤ δ * s) (hterm : |p - s * q| ≤ ε * s * q) :
    |p / (h * q) - 1| ≤ 2 * (ε + δ) := by
  have hs : s ≤ 2 * h := by
    have hlo := (abs_le.mp hcond).1
    have hhi := (abs_le.mp hcond).2
    have hs0 : 0 ≤ s := by
      by_contra hn
      have hsneg : s < 0 := lt_of_not_ge hn
      nlinarith
    nlinarith
  have hnum : |p - h * q| ≤ (ε + δ) * s * q := by
    calc
      _ = |(p - s * q) + (s - h) * q| := by congr 1; ring
      _ ≤ |p - s * q| + |(s - h) * q| := abs_add_le _ _
      _ = |p - s * q| + |h - s| * q := by rw [abs_mul, abs_of_pos hq, abs_sub_comm s h]
      _ ≤ ε * s * q + (δ * s) * q :=
        add_le_add hterm (mul_le_mul_of_nonneg_right hcond hq.le)
      _ = _ := by ring
  have hnum' : |p - h * q| ≤ 2 * (ε + δ) * (h * q) := by
    have hh' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (add_nonneg hε hδ)) hq.le
    nlinarith
  rw [show p / (h * q) - 1 = (p - h * q) / (h * q) by field_simp,
    abs_div, abs_of_pos (mul_pos hh hq)]
  exact (div_le_iff₀ (mul_pos hh hq)).mpr hnum'

end SRWTightness
