import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- A unit endpoint perturbation costs only a fixed constant in the normalized squared deficit. -/
theorem common_pair_endpoint_square_error (y B q D : ℝ)
    (hD : 1 ≤ D) (hδ : 0 ≤ B - q) (hδu : B - q ≤ 1)
    (hgap0 : 0 ≤ y - B) (hgap : y - B ≤ 5 * D) :
    -(y - B) ^ 2 / D ≤ -(y - q) ^ 2 / D + 11 := by
  have hprod : (y - B) * (B - q) ≤ 5 * D := by
    have hh := mul_le_mul hgap hδu hδ (by linarith : 0 ≤ 5 * D)
    simpa only [mul_one] using hh
  have hsq : (B - q) ^ 2 ≤ 1 := by nlinarith
  have hh : (y - q) ^ 2 - (y - B) ^ 2 ≤ 11 * D := by nlinarith
  have hdiv : ((y - q) ^ 2 - (y - B) ^ 2) / D ≤ 11 :=
    (div_le_iff₀ (by linarith : 0 < D)).mpr hh
  rw [sub_div] at hdiv
  simp only [neg_div]
  linarith

end SRWTightness
