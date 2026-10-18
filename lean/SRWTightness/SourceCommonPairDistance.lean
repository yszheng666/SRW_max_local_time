import SRWTightness.SourceCommonPairParameters

namespace SRWTightness

/-- The nonnegative distance index in the range below the outer root radius. -/
noncomputable def sourceCommonPairDistanceIndex (t ρ : ℝ) : ℕ :=
  ⌊Real.log (sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 / ρ)⌋₊

/-- The logarithmic gap used for the later common coarse endpoint. -/
noncomputable def sourceCommonPairGap (t : ℝ) : ℕ := ⌈10 * Real.log t⌉₊ + 5

/-- The later coarse endpoint, used when the distance index exceeds its gap. -/
noncomputable def sourceCommonPairLevel (t ρ : ℝ) : ℕ :=
  sourceCommonPairDistanceIndex t ρ - sourceCommonPairGap t

/-- The actual distance floor gives an exact one-unit bracket for logarithmic separation. -/
theorem source_common_pair_log_separation (t ρ : ℝ) (hρ : 0 < ρ)
    (houter : ρ ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (j J : ℕ) (hj : j + J = sourceCommonPairDistanceIndex t ρ) :
    (J : ℝ) - 1 ≤ Real.log (sourceCommonPairInnerRadius t j) - Real.log ρ ∧
      Real.log (sourceCommonPairInnerRadius t j) - Real.log ρ < J := by
  let r := sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0
  have hr : 0 < r := by
    dsimp [r, sourceRecordRadius]
    exact mul_pos (sourceLowerRadius_pos t) (Real.exp_pos _)
  have hlog : 0 ≤ Real.log (r / ρ) :=
    Real.log_nonneg ((one_le_div hρ).mpr houter)
  have hfloor := Nat.floor_le hlog
  have hceil := Nat.lt_floor_add_one (Real.log (r / ρ))
  have hcast : (j : ℝ) + J = (⌊Real.log (r / ρ)⌋₊ : ℝ) := by
    exact_mod_cast hj
  have he : Real.log (sourceCommonPairInnerRadius t j) - Real.log ρ =
      Real.log (r / ρ) - (j : ℝ) - 1 := by
    rw [Real.log_div hr.ne' hρ.ne']
    dsimp [sourceCommonPairInnerRadius, r, sourceRecordRadius]
    rw [Real.log_mul (sourceLowerRadius_pos t).ne' (Real.exp_pos _).ne',
      Real.log_mul (sourceLowerRadius_pos t).ne' (Real.exp_pos _).ne']
    simp only [Real.log_exp, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
    ring
  rw [he]
  constructor <;> linarith

/-- Natural subtraction agrees with the intended level whenever the gap fits. -/
theorem sourceCommonPairLevel_add_gap (t ρ : ℝ)
    (h : sourceCommonPairGap t ≤ sourceCommonPairDistanceIndex t ρ) :
    sourceCommonPairLevel t ρ + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ :=
  Nat.sub_add_cancel h

/-- The ceiling gap differs from ten logarithms by between five and six. -/
theorem sourceCommonPairGap_bounds (t : ℝ) (ht : 1 ≤ t) :
    10 * Real.log t + 5 ≤ (sourceCommonPairGap t : ℝ) ∧
      (sourceCommonPairGap t : ℝ) < 10 * Real.log t + 6 := by
  have hl := Nat.le_ceil (10 * Real.log t)
  have hu := Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10)
    (Real.log_nonneg ht))
  simp only [sourceCommonPairGap, Nat.cast_add, Nat.cast_ofNat]
  constructor <;> linarith

end SRWTightness
