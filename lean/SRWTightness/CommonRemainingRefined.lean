import SRWTightness.CommonQuadraticLower

namespace SRWTightness

/-- A logarithmic increment times the sublinear barrier dent has uniformly bounded ratio. -/
theorem common_log_dent_ratio (l d δ w : ℝ) (hl : 1 ≤ l) (hd : l ^ 2 ≤ d)
    (hδ : 0 ≤ δ) (hδl : δ ≤ 11 * l) (hw : w ≤ d ^ (2 / 5 : ℝ)) :
    δ * w ≤ 11 * d := by
  have hl0 : 0 < l := by linarith
  have hd0 : 0 < d := (sq_pos_of_pos hl0).trans_le hd
  have hp := Real.rpow_le_rpow (sq_nonneg l) hd (by norm_num : (0 : ℝ) ≤ 3 / 5)
  rw [← Real.rpow_two, ← Real.rpow_mul hl0.le] at hp
  have hlp := Real.rpow_le_rpow_of_exponent_le hl (by norm_num : (1 : ℝ) ≤ 2 * (3 / 5))
  rw [Real.rpow_one] at hlp
  have hlpow := hlp.trans hp
  have hδpow : δ ≤ 11 * d ^ (3 / 5 : ℝ) := by linarith
  have hh' := mul_le_mul_of_nonneg_left hw hδ
  have hh'' := mul_le_mul_of_nonneg_right hδpow (by positivity : 0 ≤ d ^ (2 / 5 : ℝ))
  calc
    δ * w ≤ δ * d ^ (2 / 5 : ℝ) := hh'
    _ ≤ (11 * d ^ (3 / 5 : ℝ)) * d ^ (2 / 5 : ℝ) := hh''
    _ = 11 * d := by rw [mul_assoc, ← Real.rpow_add hd0]; norm_num

/-- The remaining denominator costs four times its increment, plus a bounded dent correction. -/
theorem common_remaining_refined_loss (a d D δ w B : ℝ)
    (hd : 0 < d) (hD : d ≤ D) (hδ : D - d ≤ δ)
    (ha : 0 ≤ a) (hahi : a ≤ 2 * d + w) (hw : 0 ≤ w) (hwd : w ≤ d)
    (hδw : δ * w ≤ B * d) :
    a ^ 2 / d - (4 * δ + 5 * B) ≤ a ^ 2 / D := by
  have hratio : a ^ 2 ≤ (4 + 5 * w / d) * d ^ 2 := by
    have he : (4 + 5 * w / d) * d ^ 2 = 4 * d ^ 2 + 5 * w * d := by field_simp
    rw [he]
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hwd)]
  have hh := common_remaining_denominator_loss a d D δ (4 + 5 * w / d) hd hD hδ hratio
  have hpart : δ * w / d ≤ B := (div_le_iff₀ hd).mpr hδw
  have hcost : (4 + 5 * w / d) * δ ≤ 4 * δ + 5 * B := by
    calc
      _ = 4 * δ + 5 * (δ * w / d) := by ring
      _ ≤ _ := by linarith
  linarith

end SRWTightness
