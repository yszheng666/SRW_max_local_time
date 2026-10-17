import SRWTightness.RootSquareRootAffineBound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open MeasureTheory
namespace SRWTightness

/-- An integrable linear root moment controls both square-root exponentials jointly. -/
theorem root_pair_square_root_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hX0 : ∀ ω, 0 ≤ X ω)
    (hY0 : ∀ ω, 0 ≤ Y ω) (b B : ℝ) (hb : 0 < b)
    (hi : Integrable (fun ω ↦ Real.exp ((2 / b) * (X ω + Y ω))) P)
    (hlog : Real.log (∫ ω, Real.exp ((2 / b) * (X ω + Y ω)) ∂P) ≤ B) :
    Integrable (fun ω ↦ Real.exp (2 * Real.sqrt (2 * X ω) +
      2 * Real.sqrt (2 * Y ω))) P ∧
    (∫ ω, Real.exp (2 * Real.sqrt (2 * X ω) + 2 * Real.sqrt (2 * Y ω)) ∂P) ≤
      Real.exp (2 * b + B) := by
  have hpoint (ω : Ω) :
      Real.exp (2 * Real.sqrt (2 * X ω) + 2 * Real.sqrt (2 * Y ω)) ≤
        Real.exp (2 * b) * Real.exp ((2 / b) * (X ω + Y ω)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hx := root_square_root_affine_bound (X ω) b (hX0 ω) hb
    have hy := root_square_root_affine_bound (Y ω) b (hY0 ω) hb
    calc
      _ ≤ (b + 2 * X ω / b) + (b + 2 * Y ω / b) := add_le_add hx hy
      _ = _ := by ring
  have hi' := hi.const_mul (Real.exp (2 * b))
  have hf : Integrable (fun ω ↦ Real.exp (2 * Real.sqrt (2 * X ω) +
      2 * Real.sqrt (2 * Y ω))) P := by
    apply hi'.mono_nonneg (by fun_prop)
      (Filter.Eventually.of_forall (fun ω ↦ (Real.exp_pos _).le))
    exact Filter.Eventually.of_forall hpoint
  refine ⟨hf, ?_⟩
  have hM : 0 < ∫ ω, Real.exp ((2 / b) * (X ω + Y ω)) ∂P := integral_exp_pos hi
  have hbound : (∫ ω, Real.exp ((2 / b) * (X ω + Y ω)) ∂P) ≤ Real.exp B := by
    simpa only [Real.exp_log hM] using Real.exp_le_exp.mpr hlog
  calc
    _ ≤ ∫ ω, Real.exp (2 * b) * Real.exp ((2 / b) * (X ω + Y ω)) ∂P :=
      integral_mono hf hi' hpoint
    _ = Real.exp (2 * b) * ∫ ω, Real.exp ((2 / b) * (X ω + Y ω)) ∂P :=
      integral_const_mul _ _
    _ ≤ Real.exp (2 * b) * Real.exp B :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = Real.exp (2 * b + B) := (Real.exp_add _ _).symm

end SRWTightness
