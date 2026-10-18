import SRWTightness.SourceCommonPairPowerSeparation

namespace SRWTightness

/-- A logarithmic separation bracket controls the complete two-site terminal comparison term. -/
theorem log_gap_terminal_error_bound (m ρ J : ℝ) (hm : 0 < m) (hρ : 1 ≤ ρ)
    (hcut : 2 * ρ ≤ m) (hJ : 0 ≤ J)
    (hlo : J - 1 ≤ Real.log m - Real.log ρ)
    (hhi : Real.log m - Real.log ρ ≤ J) :
    (2 * ρ + 1) / m * Real.log (m / (2 * ρ)) ≤
      3 * Real.exp 1 * (J + 1) * Real.exp (-J) := by
  have hρ0 : 0 < ρ := by linarith
  have hratio : ρ / m ≤ Real.exp 1 * Real.exp (-J) := by
    calc
      _ = Real.exp (Real.log ρ - Real.log m) := by
        rw [Real.exp_sub, Real.exp_log hρ0, Real.exp_log hm]
      _ ≤ Real.exp (1 - J) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add]
  have hlog0 : 0 ≤ Real.log (m / (2 * ρ)) :=
    Real.log_nonneg ((one_le_div (by positivity)).mpr hcut)
  have hlog : Real.log (m / (2 * ρ)) ≤ J + 1 := by
    rw [Real.log_div hm.ne' (by positivity),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hρ0.ne']
    have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hr : (2 * ρ + 1) / m ≤ 3 * Real.exp 1 * Real.exp (-J) := by
    calc
      _ ≤ 3 * (ρ / m) := by apply (div_le_iff₀ hm).mpr; field_simp; nlinarith
      _ ≤ 3 * (Real.exp 1 * Real.exp (-J)) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ (3 * Real.exp 1 * Real.exp (-J)) * (J + 1) :=
      mul_le_mul hr hlog hlog0 (by positivity)
    _ = _ := by ring

/-- Actual source separation gives the literal ceiling-gap terminal comparison rate. -/
theorem source_common_terminal_literal_error (t ρ : ℝ) (j : ℕ) (ht : 1 ≤ t)
    (hρ : 1 ≤ ρ)
    (houter : ρ ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (hindex : j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ) :
    (2 * ρ + 1) / sourceCommonPairInnerRadius t j *
      Real.log (sourceCommonPairInnerRadius t j / (2 * ρ)) ≤
      3 * Real.exp 1 * ((sourceCommonPairGap t : ℝ) + 1) *
        Real.exp (-(sourceCommonPairGap t : ℝ)) := by
  have hm := sourceCommonPairInnerRadius_pos t j
  have hs := source_common_pair_log_separation t ρ (by linarith) houter j
    (sourceCommonPairGap t) hindex
  have hcut := source_common_pair_power_separation t ρ j ht (by linarith) houter hindex
  have hc : 2 * ρ ≤ sourceCommonPairInnerRadius t j :=
    hcut.trans (div_le_self hm.le (one_le_pow₀ ht))
  exact log_gap_terminal_error_bound _ ρ _ hm hρ hc (Nat.cast_nonneg _) hs.1 hs.2.le

end SRWTightness
