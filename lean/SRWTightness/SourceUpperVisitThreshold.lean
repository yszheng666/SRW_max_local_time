import SRWTightness.Targets
import SRWTightness.SourceUpperLogRadius
import Mathlib.Algebra.Order.Floor.Ring

namespace SRWTightness

/-- The manuscript upper-tail height, retaining the full s dependence. -/
noncomputable def sourceUpperHeight (t s : ℝ) : ℝ :=
  2 * t - Real.log t + Real.sqrt Real.pi * s

/-- The integer visit threshold in the upper-tail argument. -/
noncomputable def sourceUpperVisitCutoff (t s : ℝ) : ℕ :=
  Nat.ceil (sourceUpperHeight t s ^ 2 / Real.pi)

/-- The normalized upper height agrees with the original disk centering. -/
theorem sourceUpperHeight_at_radius (R s : ℝ) :
    diskCenter R + s = sourceUpperHeight (Real.log R) s / Real.sqrt Real.pi := by
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold diskCenter sourceUpperHeight
  field_simp
  <;> ring

/-- The formal cutoff is exactly the manuscript ceiling of (b_R+s)^2. -/
theorem sourceUpperVisitCutoff_at_radius (R s : ℝ) :
    sourceUpperVisitCutoff (Real.log R) s = Nat.ceil ((diskCenter R + s) ^ 2) := by
  rw [sourceUpperHeight_at_radius, div_pow, Real.sq_sqrt Real.pi_pos.le]
  rfl

/-- Green normalization exposes the same count used by the square-root comparison. -/
theorem sourceUpperVisitCutoff_green_form (t s : ℝ) :
    sourceUpperVisitCutoff t s =
      Nat.ceil ((2 / Real.pi) * sourceUpperHeight t s ^ 2 / 2) := by
  unfold sourceUpperVisitCutoff
  congr 1
  ring

end SRWTightness
