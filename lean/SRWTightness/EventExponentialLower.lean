import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory

namespace SRWTightness

/-- The conditional Jensen estimate written without division by the event probability. -/
theorem integral_exp_lower_of_integral_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (Q : α → ℝ) (C : ℝ)
    (hQ : Integrable Q μ) (hE : Integrable (fun x ↦ Real.exp (-Q x / 2)) μ)
    (hbound : ∫ x, Q x ∂μ ≤ C * μ.real Set.univ) :
    Real.exp (-C / 2) * μ.real Set.univ ≤ ∫ x, Real.exp (-Q x / 2) ∂μ := by
  have ht (x : α) : Real.exp (-C / 2) * (1 + (C - Q x) / 2) ≤ Real.exp (-Q x / 2) := by
    calc
      _ = Real.exp (-C / 2) * ((C - Q x) / 2 + 1) := by ring
      _ ≤ Real.exp (-C / 2) * Real.exp ((C - Q x) / 2) :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hI : Integrable (fun x ↦ Real.exp (-C / 2) * (1 + (C - Q x) / 2)) μ :=
    ((integrable_const 1).add (((integrable_const C).sub hQ).div_const 2)).const_mul _
  have hm := integral_mono hI hE ht
  have he : (∫ x, Real.exp (-C / 2) * (1 + (C - Q x) / 2) ∂μ) =
      Real.exp (-C / 2) * (μ.real Set.univ +
        (C * μ.real Set.univ - ∫ x, Q x ∂μ) / 2) := by
    have hsub : (∫ x, C - Q x ∂μ) = C * μ.real Set.univ - ∫ x, Q x ∂μ := by
      simpa only [integral_const, smul_eq_mul, Pi.sub_apply, Measure.real, mul_comm] using
        integral_sub (integrable_const C) hQ
    rw [integral_const_mul, integral_add (integrable_const 1)
      (show Integrable (fun x ↦ (C - Q x) / 2) μ from
        ((integrable_const C).sub hQ).div_const 2), integral_div, hsub]
    simp only [integral_const, smul_eq_mul, Measure.real, mul_one]
  rw [he] at hm
  have hp := Real.exp_pos (-C / 2)
  nlinarith

theorem event_exp_lower_of_integral_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) (Q : α → ℝ) (C : ℝ)
    (hQ : IntegrableOn Q s μ) (hE : IntegrableOn (fun x ↦ Real.exp (-Q x / 2)) s μ)
    (hbound : ∫ x in s, Q x ∂μ ≤ C * μ.real s) :
    Real.exp (-C / 2) * μ.real s ≤ ∫ x in s, Real.exp (-Q x / 2) ∂μ := by
  have hm : (μ.restrict s).real Set.univ = μ.real s := by
    simp [Measure.real]
  have hh := integral_exp_lower_of_integral_bound (μ.restrict s) Q C hQ hE
    (by rwa [hm])
  rwa [hm] at hh

end SRWTightness
