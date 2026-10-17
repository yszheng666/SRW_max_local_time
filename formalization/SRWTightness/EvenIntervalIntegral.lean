import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory
namespace SRWTightness

/-- Integrating a continuous even function over a symmetric interval doubles its positive half. -/
theorem even_interval_integral (f : ℝ → ℝ) (hf : Continuous f)
    (he : ∀ t, f (-t) = f t) (x : ℝ) :
    (∫ t in -x..x, f t) = 2 * ∫ t in 0..x, f t := by
  have hn := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := x)
  simp only [he, neg_zero] at hn
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-x) 0) (hf.intervalIntegrable 0 x), ← hn]
  ring

end SRWTightness
