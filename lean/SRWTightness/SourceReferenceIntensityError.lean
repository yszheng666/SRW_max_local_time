import SRWTightness.SourceReferenceIntensity

namespace SRWTightness

/-- The reference intensity differs from g by at most an explicit constant times H/m. -/
theorem sourceReferenceIntensity_error (m H : ℝ) (hm : 0 < m) (hH : 0 ≤ H)
    (hHm : 5 * H ≤ m) :
    0 ≤ sourceReferenceIntensity m H - (2 / Real.pi) ∧
      sourceReferenceIntensity m H - (2 / Real.pi) ≤
        (4 * (2 / Real.pi) * H) / m := by
  have he0 : 0 < Real.exp 1 := Real.exp_pos _
  have hd : 0 < m - H := by linarith
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  let u := (Real.exp 1 * m + H) / (Real.exp 1 * (m - H))
  have hu : 1 ≤ u := by
    apply (le_div_iff₀ (mul_pos he0 hd)).mpr
    nlinarith
  have hu0 : 0 < u := by linarith
  have hden : m ≤ Real.exp 1 * (m - H) := by
    have hh := mul_le_mul_of_nonneg_right Real.exp_one_gt_two.le hd.le
    nlinarith
  have hnum : (1 + Real.exp 1) * H ≤ 4 * H := by
    have hh := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hH
    nlinarith
  have hform : u - 1 = ((1 + Real.exp 1) * H) / (Real.exp 1 * (m - H)) := by
    dsimp [u]
    field_simp
    <;> ring
  have huBound : u - 1 ≤ 4 * H / m := by
    rw [hform]
    exact (div_le_div_of_nonneg_left (by positivity) hm hden).trans
      (div_le_div_of_nonneg_right hnum hm.le)
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu
  have hlogU : Real.log u ≤ 4 * H / m := (Real.log_le_sub_one_of_pos hu0).trans huBound
  have heq : sourceReferenceIntensity m H - (2 / Real.pi) = (2 / Real.pi) * Real.log u := by
    have hratio : (Real.exp 1 * m + H) / (m - H) = Real.exp 1 * u := by
      dsimp [u]
      field_simp
    unfold sourceReferenceIntensity
    rw [hratio, Real.log_mul he0.ne' hu0.ne', Real.log_exp]
    ring
  rw [heq]
  refine ⟨mul_nonneg hg.le hlog0, ?_⟩
  have hh := mul_le_mul_of_nonneg_left hlogU hg.le
  calc
    _ ≤ (2 / Real.pi) * (4 * H / m) := hh
    _ = _ := by ring

/-- Quantitative version of the alpha=g+O(m^{-1}) assertion in (5.6), with H_0=14. -/
theorem sourceReferenceIntensity_fourteen_error (m : ℝ) (hm : 70 ≤ m) :
    |sourceReferenceIntensity m 14 - (2 / Real.pi)| ≤ (56 * (2 / Real.pi)) / m := by
  have hh := sourceReferenceIntensity_error m 14 (by linarith) (by norm_num) (by linarith)
  rw [abs_of_nonneg hh.1]
  convert hh.2 using 1 <;> ring

end SRWTightness
