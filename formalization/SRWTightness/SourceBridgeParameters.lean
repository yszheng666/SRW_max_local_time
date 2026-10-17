import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace SRWTightness

/-- Explicit sufficient source scales for the two kernel-ratio hypotheses. -/
theorem sourceBridge_parameter_bounds (d H q a : ℝ) (hH : 1 ≤ H) (hd : 256 * H ≤ d)
    (ha : a ∈ Set.Icc (Real.sqrt H) (Real.sqrt H + 1))
    (hq : q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d)) :
    0 < d - H ∧ Real.sqrt H ≤ a ∧ Real.sqrt (H + (d - H)) ≤ q ∧
      2 * a * q / (d - H) ≤ 1 ∧ (a - q) ^ 2 / (2 * (d - H)) ≤ 4 := by
  have hH0 : 0 < H := by linarith
  have hd0 : 0 < d := by linarith
  have hT : 0 < d - H := by linarith
  have hrH : 1 ≤ Real.sqrt H := by simpa using Real.sqrt_le_sqrt hH
  have ha0 : 0 < a := (Real.sqrt_pos.mpr hH0).trans_le ha.1
  have hq0 : 0 < q := (Real.sqrt_pos.mpr hd0).trans_le hq.1
  have haU : a ≤ 2 * Real.sqrt H := by linarith [ha.2]
  have hr : 16 * Real.sqrt H ≤ Real.sqrt d := by
    have h := Real.sqrt_le_sqrt hd
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 256)] at h
    have h256 : Real.sqrt (256 : ℝ) = 16 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
    rwa [h256] at h
  have haq : a ≤ q := by linarith [hq.1, Real.sqrt_nonneg H]
  have hp := mul_le_mul haU hq.2 hq0.le (by positivity : 0 ≤ 2 * Real.sqrt H)
  have hp' := mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg d)
  have hsq := Real.sq_sqrt hd0.le
  have hprod : 2 * a * q ≤ d - H := by nlinarith
  have hdiff : (a - q) ^ 2 ≤ q ^ 2 := by
    nlinarith [mul_nonneg ha0.le (by linarith : 0 ≤ 2 * q - a)]
  have hqSq : q ^ 2 ≤ (2 * Real.sqrt d) ^ 2 :=
    (sq_le_sq₀ hq0.le (by positivity)).mpr hq.2
  refine ⟨hT, ha.1, ?_, ?_, ?_⟩
  · simpa using hq.1
  · exact (div_le_one hT).mpr hprod
  · apply (div_le_iff₀ (by positivity : 0 < 2 * (d - H))).mpr
    nlinarith

/-- The manuscript's endpoint window gives the positive distance a=q-b. -/
theorem sourceBridge_endpoint_distance (H q b : ℝ)
    (hb : b ∈ Set.Icc (q - Real.sqrt H - 1) (q - Real.sqrt H)) :
    q - b ∈ Set.Icc (Real.sqrt H) (Real.sqrt H + 1) := by
  constructor <;> linarith [hb.1, hb.2]

end SRWTightness
