import SRWTightness.SourceGWCoarseUpperProbability

namespace SRWTightness

/-- Uniform scalar comparison of the upper GW prefactor with the source window weight. -/
theorem gw_scalar_upper (N x u q : ℝ) (hN : 1 ≤ N) (hx1 : 1 ≤ x) (hx2 : x ≤ 2)
    (hu : N / 2 ≤ u) (huN : u ≤ 4 * N) (hq : 0 ≤ q) :
    ((5 - x) * (5 + q) / N) * Real.exp (-((x - u) ^ 2 / (2 * N))) *
        Real.sqrt (x / (u * N)) ≤
      (40 * Real.exp 8) * ((1 + q) / N ^ 2 * Real.exp (-(u ^ 2 / (2 * N)))) := by
  have hN0 : 0 < N := by linarith
  have hu0 : 0 < u := by linarith
  have hx0 : 0 ≤ x := by linarith
  have h5x : 0 ≤ 5 - x := by linarith
  have ha0 : 0 ≤ (5 - x) * (5 + q) / N := by positivity
  have ha : (5 - x) * (5 + q) / N ≤ 20 * (1 + q) / N := by
    apply div_le_div_of_nonneg_right _ hN0.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (show 0 ≤ 5 + q by linarith)]
  have hratio : x / (u * N) ≤ 4 / N ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < u * N)
      (by positivity : 0 < N ^ 2)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (sq_nonneg N),
      mul_nonneg (show 0 ≤ 2 * u - N by linarith) hN0.le]
  have hroot : Real.sqrt (x / (u * N)) ≤ 2 / N := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 / N)).mpr
    have he : (2 / N) ^ 2 = 4 / N ^ 2 := by ring
    rw [he]
    exact hratio
  have hnum : u ^ 2 - (x - u) ^ 2 ≤ 16 * N := by
    nlinarith [sq_nonneg x, mul_nonneg (sub_nonneg.mpr hx2) hu0.le]
  have hdiff : (u ^ 2 - (x - u) ^ 2) / (2 * N) ≤ 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * N)).mpr
    nlinarith
  have he : (u ^ 2 - (x - u) ^ 2) / (2 * N) =
      u ^ 2 / (2 * N) - (x - u) ^ 2 / (2 * N) := by ring
  rw [he] at hdiff
  have hexp : Real.exp (-((x - u) ^ 2 / (2 * N))) ≤
      Real.exp 8 * Real.exp (-(u ^ 2 / (2 * N))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hab := mul_le_mul ha hexp (Real.exp_nonneg _)
    (show 0 ≤ 20 * (1 + q) / N by positivity)
  have habc := mul_le_mul hab hroot (Real.sqrt_nonneg _)
    (by positivity : 0 ≤ (20 * (1 + q) / N) *
      (Real.exp 8 * Real.exp (-(u ^ 2 / (2 * N)))))
  calc
    _ ≤ (20 * (1 + q) / N * (Real.exp 8 * Real.exp (-(u ^ 2 / (2 * N))))) *
        (2 / N) := habc
    _ = _ := by ring

end SRWTightness
