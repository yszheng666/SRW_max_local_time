import SRWTightness.SourceGWWindowVariation
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

namespace SRWTightness

/-- A conditional probability on the countable GW record space is integrable. -/
theorem gw_record_probability_integrable (L : ℕ) (P : GeometricGWRecord → ℝ)
    (hP : ∀ r, P r ∈ Set.Icc (0 : ℝ) 1) : Integrable P (geometricGWRecordLaw 1 L) := by
  apply Integrable.of_bound (measurable_of_countable P).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun r ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hP r).1]
    exact (hP r).2)

/-- Terminal conditional-probability bounds integrate over a source coarse window or its band restriction. -/
theorem source_gw_window_integral_bounds (t : ℝ) (L : ℕ) (q c C : ℝ)
    (P : GeometricGWRecord → ℝ) (S : Set GeometricGWRecord)
    (hd : 0 < sourceLowerTime (sourceLowerRadius t)) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hP : ∀ r, P r ∈ Set.Icc (0 : ℝ) 1)
    (hS : S ⊆ sourceGWCoarseWindowEvent t L q)
    (hpoint : ∀ r ∈ S,
      let d := sourceLowerTime (sourceLowerRadius t)
      let q' := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
      c * (Real.exp (-2 * d - 2 * q') / d) ≤ P r ∧
        P r ≤ C * (Real.exp (-2 * d - 2 * q') / d)) :
    let d := sourceLowerTime (sourceLowerRadius t)
    let μ := geometricGWRecordLaw 1 L
    (c * (Real.exp (-2 * d - 2 * q) / d)) * μ.real S ≤ ∫ r in S, P r ∂μ ∧
      (∫ r in S, P r ∂μ) ≤
        (C * Real.exp 2 * (Real.exp (-2 * d - 2 * q) / d)) * μ.real S := by
  let d := sourceLowerTime (sourceLowerRadius t)
  let μ := geometricGWRecordLaw 1 L
  let w := Real.exp (-2 * d - 2 * q) / d
  have hSint : MeasurableSet S := Set.to_countable _ |>.measurableSet
  have hPi : IntegrableOn P S μ := (gw_record_probability_integrable L P hP).integrableOn
  have hl : ∀ r ∈ S, c * w ≤ P r := by
    intro r hr
    have hw := source_gw_terminal_weight_window t L q r hd (hS hr)
    exact (mul_le_mul_of_nonneg_left hw.1 hc).trans (hpoint r hr).1
  have hu : ∀ r ∈ S, P r ≤ C * Real.exp 2 * w := by
    intro r hr
    have hw := source_gw_terminal_weight_window t L q r hd (hS hr)
    have hh := (hpoint r hr).2.trans (mul_le_mul_of_nonneg_left hw.2 hC)
    simpa only [mul_assoc] using hh
  have hli := setIntegral_mono_on (integrable_const (c * w)).integrableOn hPi hSint hl
  have hui := setIntegral_mono_on hPi (integrable_const (C * Real.exp 2 * w)).integrableOn
    hSint hu
  rw [setIntegral_const, smul_eq_mul] at hli hui
  constructor
  · simpa only [w, d, μ, mul_comm] using hli
  · simpa only [w, d, μ, mul_comm] using hui

end SRWTightness
