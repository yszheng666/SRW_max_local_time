import SRWTightness.GWOneRootExponentialBound

open MeasureTheory
namespace SRWTightness

/-- Equation 8.23 in the source power-ratio notation, using the existing marginal interface. -/
theorem source_gw_one_root_marginal (hGW : GeometricGWOneRootMarginalInput)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} =
      (j : ℝ) ^ (k - 1) / ((j : ℝ) + 1) ^ (k + 1) := by
  rw [hGW j k hj hk]
  calc
    _ = (j : ℝ) ^ (k - 1) / (((j : ℝ) + 1) ^ 2 * ((j : ℝ) + 1) ^ (k - 1)) := by
      rw [div_pow, div_mul_div_comm, one_mul]
    _ = _ := by rw [← pow_add, show 2 + (k - 1) = k + 1 by omega]

/-- The precise exponential weight following equation 8.23 has no extra constant in its exponent. -/
theorem source_gw_one_root_exponential_bound (hGW : GeometricGWOneRootMarginalInput)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} ≤
      Real.exp (-(k : ℝ) / ((j : ℝ) + 1)) := by
  let d : ℝ := (j : ℝ) + 1
  have hd2 : 2 ≤ d := by dsimp [d]; exact_mod_cast (show 2 ≤ j + 1 by omega)
  have hd : 0 < d := by linarith
  have hc : 1 / d ^ 2 ≤ 1 - 1 / d := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    have he : (1 - 1 / d) * d ^ 2 = d ^ 2 - d := by field_simp
    rw [he]
    nlinarith
  have he : (j : ℝ) / d = 1 - 1 / d := by dsimp [d]; field_simp; ring
  have hex : (j : ℝ) / d ≤ Real.exp (-(1 / d)) := by
    rw [he]
    linarith [Real.add_one_le_exp (-(1 / d))]
  have hp := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg j) hd.le) hex (k - 1)
  have hc' : 1 / d ^ 2 ≤ Real.exp (-(1 / d)) := by
    linarith [Real.add_one_le_exp (-(1 / d))]
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
  rw [hGW j k hj hk]
  change (1 / d ^ 2) * ((j : ℝ) / d) ^ (k - 1) ≤ Real.exp (-(k : ℝ) / d)
  calc
    _ ≤ Real.exp (-(1 / d)) * Real.exp (((k - 1 : ℕ) : ℝ) * (-(1 / d))) := by
      apply mul_le_mul hc' _ (pow_nonneg (by positivity) _) (Real.exp_pos _).le
      simpa only [Real.exp_nat_mul] using hp
    _ = Real.exp (-(k : ℝ) / d) := by
      rw [← Real.exp_add, hkcast]
      congr 1
      ring

end SRWTightness
