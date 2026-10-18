import SRWTightness.SourceCommonPairDistance

namespace SRWTightness

/-- The fixed buffer changes the logarithm of the inner radius by between one and two. -/
theorem source_common_pair_buffer_log (t : ℝ) (j : ℕ)
    (hm : 14 ≤ sourceCommonPairInnerRadius t j) :
    1 + Real.log (sourceCommonPairInnerRadius t j) ≤
      Real.log (Real.exp 1 * sourceCommonPairInnerRadius t j + 14) ∧
    Real.log (Real.exp 1 * sourceCommonPairInnerRadius t j + 14) ≤
      2 + Real.log (sourceCommonPairInnerRadius t j) := by
  let m := sourceCommonPairInnerRadius t j
  have hm0 : 0 < m := sourceCommonPairInnerRadius_pos t j
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have hR : Real.exp 1 * m + 14 ≤ Real.exp 2 * m := by
    rw [he2]
    have he : Real.exp 1 + 1 ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_two]
    have hh := mul_le_mul_of_nonneg_right he hm0.le
    change 14 ≤ m at hm
    nlinarith
  have hlo := Real.log_le_log (mul_pos (Real.exp_pos 1) hm0)
    (show Real.exp 1 * m ≤ Real.exp 1 * m + 14 by linarith)
  have hhi := Real.log_le_log (show 0 < Real.exp 1 * m + 14 by positivity) hR
  rw [Real.log_mul (Real.exp_pos 1).ne' hm0.ne', Real.log_exp] at hlo
  rw [Real.log_mul (Real.exp_pos 2).ne' hm0.ne', Real.log_exp] at hhi
  exact ⟨hlo, hhi⟩

/-- The actual root-depth floor gives the inner logarithmic radius in source time. -/
theorem source_common_pair_inner_log_time (t : ℝ) (j : ℕ)
    (hscale : 32 * sourceLowerRadius t ≤ Real.exp t) :
    t - (j : ℝ) - Real.log 32 - 2 < Real.log (sourceCommonPairInnerRadius t j) ∧
      Real.log (sourceCommonPairInnerRadius t j) ≤ t - (j : ℝ) - Real.log 32 - 1 := by
  have hm := sourceLowerRadius_pos t
  have hlog : 0 ≤ Real.log (Real.exp t / (32 * sourceLowerRadius t)) :=
    Real.log_nonneg ((one_le_div (by positivity)).mpr hscale)
  have hl := Nat.floor_le hlog
  have hu := Nat.lt_floor_add_one (Real.log (Real.exp t / (32 * sourceLowerRadius t)))
  have he : Real.log (Real.exp t / (32 * sourceLowerRadius t)) =
      t - Real.log 32 - Real.log (sourceLowerRadius t) := by
    rw [Real.log_div (Real.exp_pos t).ne' (by positivity), Real.log_exp,
      Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hm.ne']
    ring
  have hi : Real.log (sourceCommonPairInnerRadius t j) = Real.log (sourceLowerRadius t) +
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) - (j : ℝ) - 1 := by
    unfold sourceCommonPairInnerRadius sourceRecordRadius
    rw [Real.log_mul hm.ne' (Real.exp_pos _).ne', Real.log_exp]
    push_cast
    ring
  change (sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) ≤ _ at hl
  change _ < (sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) + 1 at hu
  rw [he] at hl hu
  rw [hi]
  constructor <;> linarith

/-- The common killing radius is logarithmically t-j up to a fixed explicit error. -/
theorem source_common_pair_killing_log_time (t : ℝ) (j : ℕ)
    (hscale : 32 * sourceLowerRadius t ≤ Real.exp t)
    (hm : 14 ≤ sourceCommonPairInnerRadius t j) :
    t - (j : ℝ) - Real.log 32 - 1 <
      Real.log (Real.exp 1 * sourceCommonPairInnerRadius t j + 14) ∧
    Real.log (Real.exp 1 * sourceCommonPairInnerRadius t j + 14) ≤
      t - (j : ℝ) - Real.log 32 + 1 := by
  have hi := source_common_pair_inner_log_time t j hscale
  have hb := source_common_pair_buffer_log t j hm
  constructor <;> linarith [hi.1, hi.2, hb.1, hb.2]

end SRWTightness
