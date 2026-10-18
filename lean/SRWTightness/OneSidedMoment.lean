import SRWTightness.MomentInterpolation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

namespace SRWTightness

/-- Cauchy--Schwarz restricted to the positive set of a real random variable. -/
theorem integral_posPart_sq_le_measure_mul_second {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (hXm : Measurable X)
    (h2 : Integrable (fun ω ↦ (X ω) ^ 2) μ) :
    (∫ ω, (X ω)⁺ ∂μ) ^ 2 ≤ μ.real {ω | 0 < X ω} * ∫ ω, (X ω) ^ 2 ∂μ := by
  let S := {ω | 0 < X ω}
  let I : Ω → ℝ := S.indicator (fun _ ↦ 1)
  have hS : MeasurableSet S := measurableSet_lt measurable_const hXm
  have hI : MemLp I 2 μ := memLp_indicator_const 2 hS 1 (Or.inr (measure_ne_top μ S))
  have hX : MemLp X 2 μ := (memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).mpr h2
  have hIn (ω : Ω) : 0 ≤ I ω := Set.indicator_nonneg (fun _ _ ↦ zero_le_one) ω
  have hprod (ω : Ω) : I ω * |X ω| = (X ω)⁺ := by
    by_cases h : 0 < X ω
    · simp [I, S, h, abs_of_pos h, PosPart.posPart, max_eq_left h.le]
    · simp [I, S, h, PosPart.posPart, max_eq_right (le_of_not_gt h)]
  have hIsq (ω : Ω) : I ω ^ (2 : ℝ) = I ω := by
    by_cases h : ω ∈ S <;> simp [I, h]
  have hXsq (ω : Ω) : |X ω| ^ (2 : ℝ) = X ω ^ 2 := by rw [Real.rpow_two, sq_abs]
  have hb := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hIn) (Filter.Eventually.of_forall (fun ω ↦ abs_nonneg (X ω)))
    (by simpa using hI) (by simpa only [Real.norm_eq_abs, ENNReal.ofReal_ofNat] using hX.norm)
  simp_rw [hprod, hIsq, hXsq] at hb
  have hi : (∫ ω, I ω ∂μ) = μ.real S := integral_indicator_one hS
  rw [hi, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hb
  have hp : 0 ≤ ∫ ω, (X ω)⁺ ∂μ := integral_nonneg (fun ω ↦ posPart_nonneg _)
  have hm : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := integral_nonneg (fun ω ↦ sq_nonneg _)
  have hs : (Real.sqrt (μ.real S) * Real.sqrt (∫ ω, X ω ^ 2 ∂μ)) ^ 2 =
      μ.real S * ∫ ω, X ω ^ 2 ∂μ := by
    rw [mul_pow, Real.sq_sqrt (measureReal_nonneg), Real.sq_sqrt hm]
  nlinarith [Real.sqrt_nonneg (μ.real S), Real.sqrt_nonneg (∫ ω, X ω ^ 2 ∂μ)]

/-- The dimension-free one-sided fourth-moment bound used in the manuscript comparison. -/
theorem positive_probability_lower_of_centered {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (hXm : Measurable X)
    (hX : Integrable X μ) (h2 : Integrable (fun ω ↦ (X ω) ^ 2) μ)
    (h4 : Integrable (fun ω ↦ (X ω) ^ 4) μ) (hc : ∫ ω, X ω ∂μ = 0)
    (hp2 : 0 < ∫ ω, (X ω) ^ 2 ∂μ) (hp4 : 0 < ∫ ω, (X ω) ^ 4 ∂μ) :
    (∫ ω, (X ω) ^ 2 ∂μ) ^ 2 / (4 * ∫ ω, (X ω) ^ 4 ∂μ) ≤ μ.real {ω | 0 < X ω} := by
  have hi := moment_two_cubed_le_abs_one_sq_four μ X hX h2 h4 hp2 hp4
  have hs := integral_posPart_sq_le_measure_mul_second μ X hXm h2
  have ha := integral_abs_eq_two_mul_integral_posPart_sub_integral hX
  rw [hc, sub_zero] at ha
  rw [ha] at hi
  rw [div_le_iff₀ (by positivity)]
  have hb := mul_le_mul_of_nonneg_right hs hp4.le
  nlinarith

end SRWTightness
