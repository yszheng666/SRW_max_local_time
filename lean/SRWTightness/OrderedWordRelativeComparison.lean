import SRWTightness.OrderedWordCenteredIntegrals
import SRWTightness.FiniteMixtureRelative

open MeasureTheory
namespace SRWTightness

/-- Relative entrance errors control nonnegative ordered-word tests, including the empty atom. -/
theorem firstEntranceWordMark_test_relative_comparison (D K : Finset Site) (x : Site)
    (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε) (hcap : α * capacity D K ≤ 1 / 2)
    (hu : ∀ y ∈ K, |(competingEntranceLaw D K x).real {y} - α * equilibriumMeasure D K y| ≤
      ε * (α * equilibriumMeasure D K y))
    (f : WordMark → ℝ) (hf : ∀ y ∈ K, Integrable f (killedWordMarkLaw D y))
    (hn : ∀ Y, 0 ≤ f Y) :
    |(∫ Y, f Y ∂firstEntranceWordMarkLaw D K x) -
      ∫ Y, f Y ∂referenceWordMarkLaw D K α| ≤ ε * ∫ Y, f Y ∂referenceWordMarkLaw D K α := by
  have hv : ∀ y ∈ K, 0 ≤ α * equilibriumMeasure D K y :=
    fun y _ ↦ mul_nonneg hα (equilibriumMeasure_nonneg D K y)
  have hm : (∑ y ∈ K, α * equilibriumMeasure D K y) ≤ 1 / 2 := by
    rw [← Finset.mul_sum]
    exact hcap
  have hh := finite_mixture_relative_error K (fun y ↦ (competingEntranceLaw D K x).real {y})
    (fun y ↦ α * equilibriumMeasure D K y) (fun y ↦ ∫ Y, f Y ∂killedWordMarkLaw D y)
    (f none) ε (hn none) hε hv (fun y _ ↦ integral_nonneg hn) hm hu
  rw [integral_firstEntranceWordMark_centered D K x f hf,
    integral_referenceWordMark_centered D K α hα (by linarith) f hf]
  exact hh

/-- Every measurable ordered-word event inherits the same relative entrance error. -/
theorem firstEntranceWordMark_event_relative_comparison (D K : Finset Site) (x : Site)
    (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε) (hcap : α * capacity D K ≤ 1 / 2)
    (hu : ∀ y ∈ K, |(competingEntranceLaw D K x).real {y} - α * equilibriumMeasure D K y| ≤
      ε * (α * equilibriumMeasure D K y)) (s : Set WordMark) (hs : MeasurableSet s) :
    |(firstEntranceWordMarkLaw D K x).real s - (referenceWordMarkLaw D K α).real s| ≤
      ε * (referenceWordMarkLaw D K α).real s := by
  have hn : ∀ Y, 0 ≤ s.indicator (fun _ : WordMark ↦ (1 : ℝ)) Y := by
    intro Y
    by_cases hY : Y ∈ s <;> simp [Set.indicator, hY]
  have hh := firstEntranceWordMark_test_relative_comparison D K x α ε hα hε hcap hu
    (s.indicator (fun _ : WordMark ↦ (1 : ℝ)))
    (fun y _ ↦ (integrable_const (1 : ℝ)).indicator hs) hn
  have ha : (∫ Y, s.indicator (fun _ : WordMark ↦ (1 : ℝ)) Y
      ∂firstEntranceWordMarkLaw D K x) = (firstEntranceWordMarkLaw D K x).real s :=
    integral_indicator_one hs
  have hr : (∫ Y, s.indicator (fun _ : WordMark ↦ (1 : ℝ)) Y
      ∂referenceWordMarkLaw D K α) = (referenceWordMarkLaw D K α).real s :=
    integral_indicator_one hs
  rwa [ha, hr] at hh

end SRWTightness
