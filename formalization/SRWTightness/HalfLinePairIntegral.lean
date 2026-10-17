import SRWTightness.HalfLineReflectionIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory
namespace SRWTightness

/-- Pairing positive and reflected negative arguments reconstructs the full-line integral. -/
theorem half_line_pair_integral (f : ℝ → ℝ) (hf : Integrable f) :
    (∫ y in Set.Ioi (0 : ℝ), f y + f (-y)) = ∫ y, f y := by
  rw [integral_add hf.integrableOn hf.comp_neg.integrableOn]
  have he := half_line_reflection_integral (fun y ↦ f (-y)) 0 0
  simp only [zero_sub, neg_neg, neg_zero] at he
  rw [← he, add_comm]
  have hh := integral_add_compl measurableSet_Iio hf (s := Set.Iio (0 : ℝ))
  simpa only [Set.compl_Iio, integral_Ici_eq_integral_Ioi] using hh

end SRWTightness
