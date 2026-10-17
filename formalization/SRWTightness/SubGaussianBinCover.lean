import SRWTightness.SubGaussianBinEnvelope
import SRWTightness.ExternalSubGaussianMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory Set
open scoped ENNReal
namespace SRWTightness

/-- The exact positive-part moment weight in the original generic moment interface. -/
noncomputable def subGaussianPositiveWeight (b u : ℝ) : ℝ :=
  Real.exp (2 * max u 0 + b / 2 * (max u 0) ^ 2)

/-- A nonnegative upper bin weight supported on its closed lower tail. -/
noncomputable def subGaussianBinIndicator (b : ℝ) (n : ℕ) : ℝ → ℝ≥0∞ :=
  (Ici (n : ℝ)).indicator (fun _ ↦ ENNReal.ofReal (subGaussianBinWeight b n))

/-- Every indicator bin is measurable, without any regularity assumption on the probability law. -/
theorem sub_gaussian_bin_indicator_measurable (b : ℝ) (n : ℕ) :
    Measurable (subGaussianBinIndicator b n) :=
  measurable_const.indicator measurableSet_Ici

/-- The moment weight is covered pointwise by the base mass and the closed-tail bin series. -/
theorem sub_gaussian_positive_weight_bin_cover (b : ℝ) (hb : 0 < b) (u : ℝ) :
    ENNReal.ofReal (subGaussianPositiveWeight b u) ≤
      1 + ∑' n : ℕ, subGaussianBinIndicator b n u := by
  by_cases hu : 0 ≤ u
  · let N := ⌊u⌋₊
    have hn : (N : ℝ) ≤ u := Nat.floor_le hu
    have ht : u ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one u).le
    have hsq := mul_self_le_mul_self hu ht
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ b / 2)
    have he : subGaussianPositiveWeight b u ≤ subGaussianBinWeight b N := by
      unfold subGaussianPositiveWeight subGaussianBinWeight
      rw [max_eq_left hu]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hmem : u ∈ Ici (N : ℝ) := hn
    calc
      _ ≤ ENNReal.ofReal (subGaussianBinWeight b N) := ENNReal.ofReal_le_ofReal he
      _ = subGaussianBinIndicator b N u := by
        simp only [subGaussianBinIndicator, indicator_of_mem hmem]
      _ ≤ ∑' n : ℕ, subGaussianBinIndicator b n u := ENNReal.le_tsum N
      _ ≤ 1 + ∑' n : ℕ, subGaussianBinIndicator b n u :=
        le_add_of_nonneg_left (by positivity)
  · simp only [subGaussianPositiveWeight, max_eq_right (le_of_not_ge hu), mul_zero,
      zero_pow (by decide : 2 ≠ 0), add_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact le_add_of_nonneg_right (by positivity)

/-- The original sub-Gaussian closed tail controls the entire integral of each upper bin. -/
theorem sub_gaussian_bin_integral_bound (A b : ℝ) (hA : 0 < A) (hb : 0 < b)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hTail : ∀ u : ℝ, 0 ≤ u → ν.real (Ici u) ≤ A * Real.exp (-b * u ^ 2)) (n : ℕ) :
    (∫⁻ u, subGaussianBinIndicator b n u ∂ν) ≤
      ENNReal.ofReal (subGaussianBinBound A b n) := by
  change (∫⁻ u, (Ici (n : ℝ)).indicator
    (fun _ ↦ ENNReal.ofReal (subGaussianBinWeight b n)) u ∂ν) ≤ _
  rw [lintegral_indicator_const measurableSet_Ici]
  have hn := hTail (n : ℝ) (Nat.cast_nonneg n)
  have hweight : 0 ≤ subGaussianBinWeight b n := by
    unfold subGaussianBinWeight
    positivity
  have hm := mul_le_mul_of_nonneg_left hn hweight
  have he := hm.trans (sub_gaussian_bin_weight_envelope A b hA hb n)
  have hOf := ENNReal.ofReal_le_ofReal he
  rw [ENNReal.ofReal_mul hweight,
    ofReal_measureReal (measure_ne_top ν (Ici (n : ℝ)))] at hOf
  exact hOf

end SRWTightness
