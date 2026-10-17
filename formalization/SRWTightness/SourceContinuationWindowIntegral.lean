import SRWTightness.SourceContinuationWindow
import SRWTightness.TerminalWindowVariation
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
namespace SRWTightness

/-- Bounded conditional probabilities are integrable for every initial forest population. -/
theorem gw_forest_probability_integrable (k L : ℕ) (P : GeometricGWRecord → ℝ)
    (hP : ∀ r, P r ∈ Set.Icc (0 : ℝ) 1) : Integrable P (geometricGWRecordLaw k L) := by
  apply Integrable.of_bound (measurable_of_countable P).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun r ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hP r).1]
    exact (hP r).2)

/-- Terminal weights vary by at most exp(2) across a shifted unit window. -/
theorem source_continuation_weight_window (t q : ℝ) (ν L : ℕ)
    (r : GeometricGWRecord) (hd : 0 < sourceLowerTime (sourceLowerRadius t))
    (hr : r ∈ sourceContinuationWindow t ν L q) :
    let d := sourceLowerTime (sourceLowerRadius t)
    let q' := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
    Real.exp (-2 * d - 2 * q') / d ≤
      Real.exp 2 * (Real.exp (-2 * d - 2 * q) / d) := by
  have hh := hr.2
  unfold sourceTerminalRoot at hh
  exact (terminal_probability_weight_window _ _ _ hd
    (terminal_deficit_window_orientation _ _ _ hh)).2

/-- Integrate a terminal probability bound over any part of the continuation window. -/
theorem source_continuation_window_integral_upper (t q a : ℝ) (ν L k : ℕ)
    (P : GeometricGWRecord → ℝ) (S : Set GeometricGWRecord)
    (hd : 0 < sourceLowerTime (sourceLowerRadius t)) (ha : 0 ≤ a)
    (hP : ∀ r, P r ∈ Set.Icc (0 : ℝ) 1)
    (hS : S ⊆ sourceContinuationWindow t ν L q)
    (hpoint : ∀ r ∈ S,
      let d := sourceLowerTime (sourceLowerRadius t)
      let q' := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
      P r ≤ a * (Real.exp (-2 * d - 2 * q') / d)) :
    (∫ r in S, P r ∂geometricGWRecordLaw k L) ≤
      (a * Real.exp 2 * (Real.exp (-2 * sourceLowerTime (sourceLowerRadius t) - 2 * q) /
        sourceLowerTime (sourceLowerRadius t))) *
          (geometricGWRecordLaw k L).real (sourceContinuationWindow t ν L q) := by
  let μ := geometricGWRecordLaw k L
  let w := Real.exp (-2 * sourceLowerTime (sourceLowerRadius t) - 2 * q) /
    sourceLowerTime (sourceLowerRadius t)
  have hPi := (gw_forest_probability_integrable k L P hP).integrableOn (s := S)
  have hmeas : MeasurableSet S := Set.to_countable _ |>.measurableSet
  have hu : ∀ r ∈ S, P r ≤ a * Real.exp 2 * w := by
    intro r hr
    have hh := (hpoint r hr).trans (mul_le_mul_of_nonneg_left
      (source_continuation_weight_window t q ν L r hd (hS hr)) ha)
    simpa only [mul_assoc] using hh
  have hi := setIntegral_mono_on hPi (integrable_const (a * Real.exp 2 * w)).integrableOn
    hmeas hu
  rw [setIntegral_const, smul_eq_mul] at hi
  calc
    _ ≤ (a * Real.exp 2 * w) * μ.real S := by simpa only [mul_comm] using hi
    _ ≤ (a * Real.exp 2 * w) * μ.real (sourceContinuationWindow t ν L q) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hS) (by dsimp [w]; positivity)

end SRWTightness
