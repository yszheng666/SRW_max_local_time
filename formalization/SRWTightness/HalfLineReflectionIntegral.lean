import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

open MeasureTheory
namespace SRWTightness

/-- Reflection carries a lower half-line integral to the corresponding upper half-line. -/
theorem half_line_reflection_integral (f : ℝ → ℝ) (a b : ℝ) :
    (∫ t in Set.Iio a, f (b - t)) = ∫ t in Set.Ioi (b - a), f t := by
  have himage : (fun t : ℝ ↦ b - t) '' Set.Iio a = Set.Ioi (b - a) := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      change b - a < b - t
      change t < a at ht
      linarith
    · intro hu
      refine ⟨b - u, ?_, by ring⟩
      change b - u < a
      change b - a < u at hu
      linarith
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ b - t) (-1) t := by
    convert (hasDerivAt_const t b).sub (hasDerivAt_id t) using 1 <;> norm_num <;> rfl
  have hi : Set.InjOn (fun t : ℝ ↦ b - t) (Set.Iio a) := by
    intro u hu v hv huv
    linarith
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Iio
    (fun t _ ↦ (hd t).hasDerivWithinAt) hi f
  simpa only [himage, abs_neg, abs_one, one_smul] using he.symm

end SRWTightness
