import SRWTightness.FiniteMixtureRelative
import SRWTightness.ReferenceRestriction

open MeasureTheory

namespace SRWTightness

/-- Actual entrance-atom control compares all nonnegative bounded mark tests, including zero marks. -/
theorem actual_mark_test_relative_comparison (D K : Finset Site) (x : Site)
    (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε) (hcap : α * capacity D K ≤ 1 / 2)
    (hu : ∀ v ∈ K, |(competingEntranceLaw D K x).real {v} - α * equilibriumMeasure D K v| ≤
      ε * (α * equilibriumMeasure D K v))
    (F : Mark K → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ Y, ‖F Y‖ ≤ C)
    (hFn : ∀ Y, 0 ≤ F Y) :
    |markTestExpectation D K F x - ∫ Y, F Y ∂referenceMarkLaw D K α| ≤
      ε * ∫ Y, F Y ∂referenceMarkLaw D K α := by
  have ht (v : Site) : 0 ≤ markTestExpectation D K F v := integral_nonneg (fun _ ↦ hFn _)
  have hv : ∀ v ∈ K, 0 ≤ α * equilibriumMeasure D K v :=
    fun v _ ↦ mul_nonneg hα (equilibriumMeasure_nonneg D K v)
  have hm : (∑ v ∈ K, α * equilibriumMeasure D K v) ≤ 1 / 2 := by
    rw [← Finset.mul_sum]
    exact hcap
  have hh := finite_mixture_relative_error K (fun v ↦ (competingEntranceLaw D K x).real {v})
    (fun v ↦ α * equilibriumMeasure D K v) (markTestExpectation D K F)
    (F 0) ε (hFn 0) hε hv (fun v _ ↦ ht v) hm hu
  have htrue : markTestExpectation D K F x = F 0 +
      ∑ v ∈ K, (competingEntranceLaw D K x).real {v} * (markTestExpectation D K F v - F 0) := by
    have h := markTestExpectation_entrance_decomposition D K F hF C hC x
    linarith
  have hs : (∑ v ∈ K, (α * equilibriumMeasure D K v) * (markTestExpectation D K F v - F 0)) =
      α * ∑ v ∈ K, equilibriumMeasure D K v * (markTestExpectation D K F v - F 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [htrue, integral_reference_centered D K α hα (by linarith) F hF C hC, ← hs]
  exact hh

end SRWTightness
