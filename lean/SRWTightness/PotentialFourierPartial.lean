import SRWTightness.FourierCharacteristicDecay
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

noncomputable def potentialFourierPartial (z : Site) (N : ℕ) (θ : ℝ × ℝ) : ℝ :=
  potentialFourierIntegrand z θ * (1 - fourierCharacteristic θ ^ N)

theorem measurable_potentialFourierPartial (z : Site) (N : ℕ) :
    Measurable (potentialFourierPartial z N) :=
  (measurable_potentialFourierIntegrand z).mul
    (measurable_const.sub (measurable_fourierCharacteristic.pow_const N))

theorem norm_potentialFourierPartial_le (z : Site) (N : ℕ) (θ : ℝ × ℝ) :
    ‖potentialFourierPartial z N θ‖ ≤ 2 * potentialFourierIntegrand z θ := by
  have hp : |fourierCharacteristic θ ^ N| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_fourierCharacteristic_le_one θ)
  have hb : |1 - fourierCharacteristic θ ^ N| ≤ 2 := by
    have hh := norm_sub_le (1 : ℝ) (fourierCharacteristic θ ^ N)
    simp only [Real.norm_eq_abs, abs_one] at hh
    linarith
  unfold potentialFourierPartial
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (potentialFourierIntegrand_nonneg z θ), Real.norm_eq_abs]
  calc
    _ ≤ potentialFourierIntegrand z θ * 2 :=
      mul_le_mul_of_nonneg_left hb (potentialFourierIntegrand_nonneg z θ)
    _ = _ := mul_comm _ _

theorem integrable_potentialFourierPartial (z : Site) (N : ℕ) :
    Integrable (potentialFourierPartial z N) fourierBoxMeasure :=
  ((integrable_potentialFourierIntegrand z).const_mul 2).mono'
    (measurable_potentialFourierPartial z N).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_potentialFourierPartial_le z N))

theorem potentialFourierPartial_eq_sum (z : Site) (N : ℕ) (θ : ℝ × ℝ)
    (hθ : fourierDenominator θ ≠ 0) :
    potentialFourierPartial z N θ =
      ∑ i ∈ Finset.range N, fourierCharacteristic θ ^ i * (1 - Real.cos (fourierPhase z θ)) := by
  have hn : 1 - fourierCharacteristic θ ≠ 0 := hθ
  unfold potentialFourierPartial potentialFourierIntegrand
  change (1 - Real.cos (fourierPhase z θ)) / (1 - fourierCharacteristic θ) *
    (1 - fourierCharacteristic θ ^ N) = _
  rw [← geom_sum_mul_neg, ← Finset.sum_mul]
  field_simp

theorem potentialFourierPartial_integral_tendsto (z : Site) :
    Tendsto (fun N : ℕ ↦ ∫ θ, potentialFourierPartial z N θ ∂fourierBoxMeasure) atTop
      (𝓝 (∫ θ, potentialFourierIntegrand z θ ∂fourierBoxMeasure)) := by
  apply tendsto_integral_of_dominated_convergence (fun θ ↦ 2 * potentialFourierIntegrand z θ)
    (fun N ↦ (measurable_potentialFourierPartial z N).aestronglyMeasurable)
    ((integrable_potentialFourierIntegrand z).const_mul 2)
    (fun N ↦ Filter.Eventually.of_forall (norm_potentialFourierPartial_le z N))
  filter_upwards [fourierCharacteristic_ae_pow_tendsto_zero] with θ hθ
  have h1 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hI : Tendsto (fun _ : ℕ ↦ potentialFourierIntegrand z θ) atTop
      (𝓝 (potentialFourierIntegrand z θ)) := tendsto_const_nhds
  simpa only [potentialFourierPartial, sub_zero, mul_one] using hI.mul (h1.sub hθ)

end SRWTightness
