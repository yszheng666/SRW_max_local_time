import SRWTightness.ActualMarkRelativeComparison

open MeasureTheory

namespace SRWTightness

/-- Actual and reference mark probabilities obey the same relative bound for every measurable event. -/
theorem actual_mark_event_relative_comparison (D K : Finset Site) (x : Site)
    (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε) (hcap : α * capacity D K ≤ 1 / 2)
    (hu : ∀ v ∈ K, |(competingEntranceLaw D K x).real {v} - α * equilibriumMeasure D K v| ≤
      ε * (α * equilibriumMeasure D K v))
    (s : Set (Mark K)) (hs : MeasurableSet s) :
    |(killedMarkLaw D K x).real s - (referenceMarkLaw D K α).real s| ≤
      ε * (referenceMarkLaw D K α).real s := by
  classical
  let F : Mark K → ℝ := s.indicator (fun _ ↦ 1)
  have hF : Measurable F := measurable_const.indicator hs
  have hC : ∀ Y, ‖F Y‖ ≤ 1 := by
    intro Y
    by_cases hY : Y ∈ s <;> simp [F, hY]
  have hFn : ∀ Y, 0 ≤ F Y := by
    intro Y
    by_cases hY : Y ∈ s <;> simp [F, hY]
  have ht : markTestExpectation D K F x = (killedMarkLaw D K x).real s := by
    calc
      _ = ∫ Y, F Y ∂killedMarkLaw D K x :=
        (integral_map (measurable_killedMark D K x).aemeasurable hF.aestronglyMeasurable).symm
      _ = _ := integral_indicator_one hs
  have hr : (∫ Y, F Y ∂referenceMarkLaw D K α) = (referenceMarkLaw D K α).real s :=
    integral_indicator_one hs
  have hh := actual_mark_test_relative_comparison D K x α ε hα hε hcap hu F hF 1 hC hFn
  rwa [ht, hr] at hh

end SRWTightness
