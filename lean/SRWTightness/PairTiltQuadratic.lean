import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.AbsoluteValue.Basic

namespace SRWTightness

/-- Half the covariance quadratic form for the signed tilt (2,2,-2). -/
theorem pair_tilt_quadratic_identity (Vz Vw c v e : ℝ) :
    (4 * Vz + 4 * Vw + 4 * (v - e) + 8 * c - 8 * v - 8 * v) / 2 =
      2 * Vz + 2 * Vw + 4 * c - 6 * v - 2 * e := by ring

/-- The leading signed-tilt cumulant is 4d-2v with a uniform error from the actual covariance entries. -/
theorem pair_tilt_quadratic_error (Vz Vw c v e d Cz Cw Cc Ce : ℝ)
    (hz : |Vz - d| ≤ Cz) (hw : |Vw - d| ≤ Cw)
    (hc : |c - v| ≤ Cc) (he : |e| ≤ Ce) :
    |(4 * Vz + 4 * Vw + 4 * (v - e) + 8 * c - 8 * v - 8 * v) / 2 -
      (4 * d - 2 * v)| ≤ 2 * Cz + 2 * Cw + 4 * Cc + 2 * Ce := by
  rw [pair_tilt_quadratic_identity]
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  obtain ⟨hw1, hw2⟩ := abs_le.mp hw
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  obtain ⟨he1, he2⟩ := abs_le.mp he
  apply abs_le.mpr
  constructor <;> linarith

end SRWTightness
