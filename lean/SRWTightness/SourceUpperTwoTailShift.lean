import SRWTightness.SourceUpperShiftedTail

namespace SRWTightness

/-- A fixed nonnegative shift preserves both distinct tail shapes after enlarging their common constant. -/
theorem source_upper_two_tail_shift (d s : ℝ) (hd : 0 ≤ d) :
    (1 + (s - d)) * Real.exp (-(2 * Real.sqrt Real.pi * (s - d))) +
      Real.exp (-3 * (s - d) / 2) ≤
        Real.exp (2 * Real.sqrt Real.pi * d) *
          ((1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) + Real.exp (-3 * s / 2)) := by
  have he : Real.exp (-(2 * Real.sqrt Real.pi * (s - d))) =
      Real.exp (2 * Real.sqrt Real.pi * d) * Real.exp (-(2 * Real.sqrt Real.pi * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfirst : (1 + (s - d)) * Real.exp (-(2 * Real.sqrt Real.pi * (s - d))) ≤
      Real.exp (2 * Real.sqrt Real.pi * d) *
        ((1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s))) := by
    calc
      _ ≤ (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * (s - d))) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = _ := by rw [he]; ring
  have he2 : Real.exp (-3 * (s - d) / 2) =
      Real.exp (3 * d / 2) * Real.exp (-3 * s / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsecond : Real.exp (-3 * (s - d) / 2) ≤
      Real.exp (2 * Real.sqrt Real.pi * d) * Real.exp (-3 * s / 2) := by
    rw [he2]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right source_upper_height_exponent_ge hd
    nlinarith only [hh]
  calc
    _ ≤ _ := add_le_add hfirst hsecond
    _ = _ := by ring

end SRWTightness
