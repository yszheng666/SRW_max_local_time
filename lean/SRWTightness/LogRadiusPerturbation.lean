import SRWTightness.LogRadiusOvershoot

namespace SRWTightness

/-- Logarithmic error for a radial perturbation smaller than half the reference radius. -/
theorem log_radius_perturbation (r R H : ℝ) (hH : 0 < H) (hR : 2 * H ≤ R)
    (hrl : R - H ≤ r) (hru : r ≤ R + H) :
    |Real.log r - Real.log R| ≤ 2 * H / R := by
  have hR0 : 0 < R := by linarith
  have hr0 : 0 < r := by linarith
  have hh := log_radius_unit_error (r / H) (R / H)
    ((le_div_iff₀ hH).mpr hR)
    (by apply (le_div_iff₀ hH).mpr; field_simp; nlinarith)
    (by apply (div_le_iff₀ hH).mpr; field_simp; nlinarith)
  rw [Real.log_div hr0.ne' hH.ne', Real.log_div hR0.ne' hH.ne'] at hh
  convert hh using 1
  · congr 1
    ring
  · field_simp

/-- Two uniform errors control deviation from the midpoint probability. -/
theorem probability_half_of_log_errors (p D N E F : ℝ) (hD : 1 ≤ D)
    (hE : |p * D - N| ≤ E) (hF : |N - D / 2| ≤ F) :
    |p - 1 / 2| ≤ E + F := by
  have hEF : 0 ≤ E + F := add_nonneg ((abs_nonneg _).trans hE) ((abs_nonneg _).trans hF)
  have hEL := (abs_le.mp hE).1
  have hEU := (abs_le.mp hE).2
  have hFL := (abs_le.mp hF).1
  have hFU := (abs_le.mp hF).2
  apply abs_le.mpr
  constructor
  · by_contra hh
    have hp : p - 1 / 2 < -(E + F) := lt_of_not_ge hh
    nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - p by linarith) (sub_nonneg.mpr hD)]
  · by_contra hh
    have hp : E + F < p - 1 / 2 := lt_of_not_ge hh
    nlinarith [mul_nonneg (show 0 ≤ p - 1 / 2 by linarith) (sub_nonneg.mpr hD)]

end SRWTightness
