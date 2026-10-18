import SRWTightness.CommonQuadraticIdentity

namespace SRWTightness

/-- The total-time perturbation costs only a constant in the leading squared-height term. -/
theorem common_height_square_lower (t T l E : ℝ) (hT : 0 < T) (he : T - t ≤ E) :
    4 * t - 4 * l - 4 * E ≤ (2 * t - l) ^ 2 / T := by
  apply (le_div_iff₀ hT).mpr
  have hh := mul_nonneg (sub_nonneg.mpr he) hT.le
  nlinarith [sq_nonneg (l + 2 * (T - t))]

/-- The exact coarse exponent has the manuscript lower bound before denominator perturbation. -/
theorem common_quadratic_lower (t T l E θ j w : ℝ)
    (hj : 0 < j) (hrem : 0 < T - j) (he : T - t ≤ E)
    (hθ : 0 ≤ θ) (hθ2 : θ ≤ 2) (hy : θ * T = 2 * t - l)
    (hw : 2 * w - 1 ≤ θ * w) :
    4 * t - 2 * j + 2 * w - 4 * l - (4 * E + 9) ≤
      (θ * j + (4 - w)) ^ 2 / (2 * j) +
        (2 * t - l - (θ * j + (4 - w))) ^ 2 / (T - j) := by
  have hT : 0 < T := by linarith
  have hlead : 4 * t - 4 * l - 4 * E ≤ θ ^ 2 * T := by
    have hh := common_height_square_lower t T l E hT he
    rw [← hy] at hh
    convert hh using 1 <;> field_simp <;> ring
  have hsq : θ ^ 2 ≤ 4 := by nlinarith
  have hjloss := mul_le_mul_of_nonneg_right hsq hj.le
  have hpositive : 0 ≤ (4 - w) ^ 2 * (1 / (2 * j) + 1 / (T - j)) := by positivity
  rw [← hy, common_quadratic_identity θ T j (4 - w) hj.ne' hrem.ne']
  nlinarith

/-- Enlarging the generation denominator by one has a bounded square cost. -/
theorem common_generation_denominator_loss (q j B : ℝ)
    (hj : 0 < j) (hq : q ^ 2 ≤ B * j * (j + 1)) :
    q ^ 2 / (2 * j) - B / 2 ≤ q ^ 2 / (2 * (j + 1)) := by
  have hj1 : 0 < j + 1 := by linarith
  apply (le_div_iff₀ (by positivity : 0 < 2 * (j + 1))).mpr
  have hid : (q ^ 2 / (2 * j) - B / 2) * (2 * (j + 1)) =
      q ^ 2 + (q ^ 2 - B * j * (j + 1)) / j := by field_simp; ring
  rw [hid]
  have hh : (q ^ 2 - B * j * (j + 1)) / j ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hq) hj.le
  linarith

/-- A larger remaining-time denominator costs at most its increment times the squared ratio. -/
theorem common_remaining_denominator_loss (a d D δ M : ℝ)
    (hd : 0 < d) (hD : d ≤ D) (hδ : D - d ≤ δ)
    (hratio : a ^ 2 ≤ M * d ^ 2) :
    a ^ 2 / d - M * δ ≤ a ^ 2 / D := by
  have hD0 : 0 < D := hd.trans_le hD
  have hM : 0 ≤ M := by
    by_contra hh
    have hh' : M * d ^ 2 < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hh) (sq_pos_of_pos hd)
    nlinarith [sq_nonneg a]
  have hδ0 : 0 ≤ δ := by linarith
  have hp := mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr hD)
  have hinc := mul_le_mul_of_nonneg_left hδ (mul_nonneg hM (sq_nonneg d))
  have hden := mul_le_mul_of_nonneg_left hD (mul_nonneg (mul_nonneg hM hδ0) hd.le)
  apply (le_div_iff₀ hD0).mpr
  apply (mul_le_mul_iff_of_pos_right hd).mp
  have hid : ((a ^ 2 / d - M * δ) * D) * d = a ^ 2 * D - M * δ * D * d := by
    field_simp
  rw [hid]
  nlinarith

end SRWTightness
