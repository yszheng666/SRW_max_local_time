import SRWTightness.ExternalMarkedGWTree

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Uniform bounds on permitted record fibers pass to arbitrary countable record events. -/
theorem countable_record_event_comparison {Ω R : Type*} [MeasurableSpace Ω] [Countable R]
    (μ : Measure Ω) (f : Ω → R) (q : R → ℝ≥0∞) (s : Set R) (L U : ℝ≥0∞)
    (hf : ∀ r ∈ s, MeasurableSet (f ⁻¹' {r}))
    (h : ∀ r ∈ s, L * q r ≤ μ (f ⁻¹' {r}) ∧ μ (f ⁻¹' {r}) ≤ U * q r) :
    L * (∑' r : s, q r) ≤ μ (f ⁻¹' s) ∧
      μ (f ⁻¹' s) ≤ U * (∑' r : s, q r) := by
  rw [← tsum_measure_preimage_singleton s.to_countable hf]
  constructor
  · rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum (fun r ↦ (h r r.property).1)
  · rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum (fun r ↦ (h r r.property).2)

/-- Real exponential fiber bounds give event bounds when record errors are uniformly bounded. -/
theorem countable_record_event_exponential {Ω R : Type*} [MeasurableSpace Ω] [Countable R]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → R) (q e : R → ℝ)
    (s : Set R) (E : ℝ) (hq : ∀ r, 0 ≤ q r)
    (hf : ∀ r ∈ s, MeasurableSet (f ⁻¹' {r}))
    (he : ∀ r ∈ s, e r ≤ E)
    (h : ∀ r ∈ s,
      Real.exp (-e r) * q r ≤ μ.real (f ⁻¹' {r}) ∧
      μ.real (f ⁻¹' {r}) ≤ Real.exp (e r) * q r) :
    ENNReal.ofReal (Real.exp (-E)) * (∑' r : s, ENNReal.ofReal (q r)) ≤ μ (f ⁻¹' s) ∧
      μ (f ⁻¹' s) ≤ ENNReal.ofReal (Real.exp E) *
        (∑' r : s, ENNReal.ofReal (q r)) := by
  apply countable_record_event_comparison μ f (fun r ↦ ENNReal.ofReal (q r)) s _ _ hf
  intro r hr
  have hlo : Real.exp (-E) * q r ≤ μ.real (f ⁻¹' {r}) :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (he r hr))) (hq r)).trans
      (h r hr).1
  have hhi : μ.real (f ⁻¹' {r}) ≤ Real.exp E * q r :=
    (h r hr).2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (he r hr)) (hq r))
  constructor
  · simpa only [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_measureReal (measure_ne_top μ _)] using
      ENNReal.ofReal_le_ofReal hlo
  · simpa only [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_measureReal (measure_ne_top μ _)] using
      ENNReal.ofReal_le_ofReal hhi

end SRWTightness
