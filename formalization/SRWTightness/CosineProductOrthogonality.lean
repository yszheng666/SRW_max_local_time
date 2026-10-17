import SRWTightness.FourierCosineMoments

open MeasureTheory

namespace SRWTightness

theorem fourierInterval_integral_cos_mul (k l : ℤ) :
    (∫ t, Real.cos ((k : ℝ) * t) * Real.cos ((l : ℝ) * t) ∂fourierIntervalMeasure) =
      Real.pi * ((if k + l = 0 then 1 else 0) + (if k - l = 0 then 1 else 0)) := by
  have he (t : ℝ) : Real.cos ((k : ℝ) * t) * Real.cos ((l : ℝ) * t) =
      (Real.cos (((k + l : ℤ) : ℝ) * t) + Real.cos (((k - l : ℤ) : ℝ) * t)) / 2 := by
    simp only [Int.cast_add, Int.cast_sub, add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring
  simp_rw [he]
  rw [integral_div, integral_add]
  · rw [fourierInterval_integral_cos, fourierInterval_integral_cos]
    split_ifs <;> ring
  · exact (show Continuous (fun t : ℝ ↦ Real.cos (((k + l : ℤ) : ℝ) * t)) by fun_prop).integrableOn_Icc
  · exact (show Continuous (fun t : ℝ ↦ Real.cos (((k - l : ℤ) : ℝ) * t)) by fun_prop).integrableOn_Icc

end SRWTightness
