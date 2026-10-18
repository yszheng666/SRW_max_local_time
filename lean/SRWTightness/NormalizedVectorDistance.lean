import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Distance splits into a radial part and a normalized angular part. -/
theorem normalized_vector_distance_identity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖u - v‖ ^ 2 = (‖u‖ - ‖v‖) ^ 2 + ‖u‖ * ‖v‖ *
      ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖ ^ 2 := by
  have ha : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hb : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    real_inner_smul_left, real_inner_smul_right]
  field_simp
  <;> ring

/-- Normalization loses at most the reciprocal of the smaller input norm. -/
theorem normalized_vector_distance_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖ ≤ ‖u - v‖ / min ‖u‖ ‖v‖ := by
  have ha : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hb : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hm : 0 < min ‖u‖ ‖v‖ := lt_min ha hb
  have hp : (min ‖u‖ ‖v‖) ^ 2 ≤ ‖u‖ * ‖v‖ := by
    rcases le_total ‖u‖ ‖v‖ with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have he := normalized_vector_distance_identity u v hu hv
  have hh := mul_le_mul_of_nonneg_right hp
    (sq_nonneg ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖)
  apply (le_div_iff₀ hm).mpr
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hm.le) (norm_nonneg _)).mp
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

end SRWTightness
