import SRWTightness.DiskEquilibriumErrorScales

namespace SRWTightness

/-- Any radius growing at least dyadically has the same summable weight bound. -/
theorem equilibriumWeight_geometric_radius_upper (b : Site) (A R a : ℝ)
    (hA : 4 ≤ A) (i : ℕ) (ha : A * 2 ^ i ≤ a) (hsep : 2 * a ≤ R) (x : Site) :
    equilibriumWeight (translateFinset b (diskFinset R))
      (translateFinset b (diskFinset a)) x ≤
        (diskEquilibriumWeightConstant / A) * (1 / 2 : ℝ) ^ i := by
  have hA0 : 0 < A := by linarith
  have hp : 1 ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  have ha4 : 4 ≤ a := by nlinarith
  have hh := equilibriumWeight_translated_radius_upper b a R ha4 hsep x
  calc
    _ ≤ diskEquilibriumWeightConstant / a := hh
    _ ≤ diskEquilibriumWeightConstant / (A * (2 : ℝ) ^ i) :=
      div_le_div_of_nonneg_left diskEquilibriumWeightConstant_pos.le (by positivity) ha
    _ = (diskEquilibriumWeightConstant / A) * (1 / 2 : ℝ) ^ i := by
      rw [one_div_pow, div_mul_eq_div_mul_one_div]

theorem equilibriumWeight_geometric_ratio_upper (b : Site) (A R q : ℝ)
    (hA : 4 ≤ A) (hq : 2 ≤ q) (i : ℕ) (hsep : 2 * (A * q ^ i) ≤ R) (x : Site) :
    equilibriumWeight (translateFinset b (diskFinset R))
      (translateFinset b (diskFinset (A * q ^ i))) x ≤
        (diskEquilibriumWeightConstant / A) * (1 / 2 : ℝ) ^ i := by
  apply equilibriumWeight_geometric_radius_upper b A R _ hA i _ hsep x
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hq i) (by linarith)

/-- The actual covariance loss at each disk radius is bounded by an inverse radius. -/
theorem equilibriumDiscreteError_translated_radius_upper (b : Site) (a R g : ℝ)
    (ha : 4 ≤ a) (hRa : 2 * a ≤ R) (hg : 0 < g) :
    equilibriumDiscreteError (translateFinset b (diskFinset R))
      (translateFinset b (diskFinset a)) g ≤ (diskEquilibriumWeightConstant / a) / (2 * g) := by
  unfold equilibriumDiscreteError
  exact div_le_div_of_nonneg_right
    (equilibriumWeight_translated_sq_sum_upper b a R ha hRa) (by positivity)

end SRWTightness
