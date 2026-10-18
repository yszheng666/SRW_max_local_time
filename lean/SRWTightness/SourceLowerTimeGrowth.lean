import SRWTightness.SourceScaleThreshold

namespace SRWTightness

theorem sourceScaleThreshold_log_lower (A t : ℝ) (ht : sourceScaleThreshold A ≤ t) :
    1 ≤ Real.log t := by
  have hh : Real.exp (max 10 (1 + sourceLowerTimeError)) ≤ t := (le_max_right _ _).trans ht
  have hl := Real.log_le_log (Real.exp_pos _) hh
  rw [Real.log_exp] at hl
  have hm : (10 : ℝ) ≤ max 10 (1 + sourceLowerTimeError) := le_max_left _ _
  linarith

theorem sourceLowerLogRadius_cube_upper (t : ℝ) (ht : 1 ≤ Real.log t) :
    sourceLowerLogRadius t ≤ (2000 * Real.log t) ^ 3 := by
  have hx : 1 ≤ 2000 * Real.log t := by linarith
  have hh := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (5 / 2 : ℝ) ≤ 3)
  have he : (2000 * Real.log t) ^ (3 : ℝ) = (2000 * Real.log t) ^ (3 : ℕ) :=
    Real.rpow_natCast _ 3
  rw [he] at hh
  exact hh

/-- A polynomial-log majorant for the actual Green-function time d. -/
theorem sourceLowerTime_square_upper (t : ℝ) (ht : sourceScaleThreshold 4 ≤ t) :
    0 ≤ sourceLowerTime (sourceLowerRadius t) ∧
      sourceLowerTime (sourceLowerRadius t) ^ 2 ≤
        2 * (2000 * Real.log t) ^ 6 + 2 * sourceLowerTimeError ^ 2 := by
  obtain ⟨ht2, _, hm70, hdlog⟩ := sourceScaleThreshold_conditions t 4 (by norm_num) ht
  have hlt := sourceScaleThreshold_log_lower 4 t ht
  have hd := sourceLowerTime_log_bound (sourceLowerRadius t) (by linarith)
  rw [log_sourceLowerRadius] at hd hdlog
  obtain ⟨hdl, hdu⟩ := abs_le.mp hd
  have hd0 : 0 ≤ sourceLowerTime (sourceLowerRadius t) := by linarith
  have hD0 : 0 ≤ sourceLowerLogRadius t := by
    unfold sourceLowerLogRadius
    exact Real.rpow_nonneg (by linarith) _
  have hcube := sourceLowerLogRadius_cube_upper t hlt
  have hs1 := pow_le_pow_left₀ hd0
    (show sourceLowerTime (sourceLowerRadius t) ≤ sourceLowerLogRadius t + sourceLowerTimeError by linarith) 2
  have hs2 : sourceLowerLogRadius t ^ 2 ≤ (2000 * Real.log t) ^ 6 := by
    calc
      _ ≤ ((2000 * Real.log t) ^ 3) ^ 2 := pow_le_pow_left₀ hD0 hcube 2
      _ = _ := by ring
  refine ⟨hd0, ?_⟩
  nlinarith [sq_nonneg (sourceLowerLogRadius t - sourceLowerTimeError)]

end SRWTightness
