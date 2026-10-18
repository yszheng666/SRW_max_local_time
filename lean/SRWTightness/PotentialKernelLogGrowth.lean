import SRWTightness.PotentialKernelLogFinite

namespace SRWTightness

theorem potentialKernel_log_upper (z : Site) (hz : 1 ≤ normSq z) :
    potentialKernel z ≤ Real.log (normSq z) / Real.pi + 1 + 1 / Real.pi + 2 * Real.pi := by
  let N := ⌊normSq z⌋₊
  have hN : 1 ≤ N := (Nat.one_le_floor_iff _).mpr hz
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hfloor : (N : ℝ) ≤ normSq z := Nat.floor_le (by linarith)
  have hlt : normSq z < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlog : Real.log (N : ℝ) ≤ Real.log (normSq z) := Real.log_le_log hNpos hfloor
  have hratio : Real.pi * normSq z / N ≤ 2 * Real.pi := by
    apply (div_le_iff₀ hNpos).2
    nlinarith [Real.pi_pos]
  have h := potentialKernel_log_upper_finite z N (by omega)
  have hl := div_le_div_of_nonneg_right hlog Real.pi_pos.le
  linarith

theorem potentialKernel_log_lower (z : Site) (hz : 1 ≤ normSq z) :
    Real.log (normSq z) / Real.pi - (2 + 16 * Real.exp 1 / Real.pi) ≤ potentialKernel z := by
  let N := ⌊normSq z⌋₊
  have hN : 1 ≤ N := (Nat.one_le_floor_iff _).mpr hz
  have hx : 0 < normSq z := by linarith
  have hfloor : (N : ℝ) ≤ normSq z := Nat.floor_le hx.le
  have hlt : normSq z < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlog : Real.log (normSq z) ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hx hlt.le
  have hratio : ((2 * N : ℕ) : ℝ) * ((8 * Real.exp 1) / (Real.pi * normSq z)) ≤
      16 * Real.exp 1 / Real.pi := by
    push_cast
    rw [← mul_div_assoc, div_le_div_iff₀ (mul_pos Real.pi_pos hx) Real.pi_pos]
    nlinarith [mul_nonneg Real.pi_pos.le (mul_nonneg (Real.exp_pos (1 : ℝ)).le (sub_nonneg.mpr hfloor))]
  have h := potentialKernel_log_lower_finite z hx N (by omega)
  have hl := div_le_div_of_nonneg_right hlog Real.pi_pos.le
  linarith

end SRWTightness
