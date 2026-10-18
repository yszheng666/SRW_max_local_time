import SRWTightness.SourceGWCoarseLowerProbability

namespace SRWTightness

/-- Uniform scalar comparison of the lower GW prefactor with the source window weight. -/
theorem gw_scalar_lower (N x u b q : ℝ) (hN : 1 ≤ N) (hx1 : 1 ≤ x) (hx2 : x ≤ 2)
    (hu : 2 ≤ u) (hyN : u + 1 / 4 ≤ 4 * N) (hq : 0 ≤ q)
    (hm : q / 2 ≤ b - (u + 1 / 4)) :
    (1 + q) / (2 * N ^ 2) * Real.exp (-(u ^ 2 / (2 * N))) ≤
      ((5 - x) * (1 + b - (u + 1 / 4)) / N) *
        Real.exp (-((x - (u + 1 / 4)) ^ 2 / (2 * N))) *
        min (Real.sqrt (x / ((u + 1 / 4) * N))) 1 := by
  have hN0 : 0 < N := by linarith
  have hy0 : 0 < u + 1 / 4 := by linarith
  have hm0 : 0 ≤ 1 + b - (u + 1 / 4) := by linarith
  have h5x : 0 ≤ 5 - x := by linarith
  have ha0 : 0 ≤ (5 - x) * (1 + b - (u + 1 / 4)) / N := by positivity
  have ha : (1 + q) / N ≤ (5 - x) * (1 + b - (u + 1 / 4)) / N := by
    apply div_le_div_of_nonneg_right _ hN0.le
    nlinarith [mul_nonneg (show 0 ≤ 2 - x by linarith) hm0]
  have hsquare : (x - (u + 1 / 4)) ^ 2 ≤ u ^ 2 := by nlinarith
  have hexp := Real.exp_le_exp.mpr (neg_le_neg
    (div_le_div_of_nonneg_right hsquare (show 0 ≤ 2 * N by positivity)))
  have hratio : 1 / (4 * N ^ 2) ≤ x / ((u + 1 / 4) * N) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * N ^ 2)
      (by positivity : 0 < (u + 1 / 4) * N)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sq_nonneg N),
      mul_nonneg (sub_nonneg.mpr hyN) hN0.le]
  have hroot : 1 / (2 * N) ≤ Real.sqrt (x / ((u + 1 / 4) * N)) := by
    apply Real.le_sqrt_of_sq_le
    have he : (1 / (2 * N)) ^ 2 = 1 / (4 * N ^ 2) := by ring
    rw [he]
    exact hratio
  have hmin : 1 / (2 * N) ≤ min (Real.sqrt (x / ((u + 1 / 4) * N))) 1 := by
    exact le_min hroot ((div_le_one (by positivity : 0 < 2 * N)).mpr (by linarith))
  have hab := mul_le_mul ha hexp (Real.exp_nonneg _) ha0
  have habc := mul_le_mul hab hmin (by positivity : 0 ≤ 1 / (2 * N))
    (mul_nonneg ha0 (Real.exp_nonneg _))
  calc
    _ = ((1 + q) / N * Real.exp (-(u ^ 2 / (2 * N)))) * (1 / (2 * N)) := by ring
    _ ≤ _ := habc

end SRWTightness
