import SRWTightness.OrderedWordCenteredIntegrals

open MeasureTheory
namespace SRWTightness

/-- Upper empty-atom and entrance-weight bounds control every nonnegative ordered test. -/
theorem firstEntranceWordMark_test_uniform_upper (D K : Finset Site) (x : Site)
    (α U : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (hzero : competingExitMass D K x ≤ U * (1 - α * capacity D K))
    (hu : ∀ y ∈ K, (competingEntranceLaw D K x).real {y} ≤
      U * (α * equilibriumMeasure D K y))
    (f : WordMark → ℝ) (hf : ∀ y ∈ K, Integrable f (killedWordMarkLaw D y))
    (hn : ∀ Y, 0 ≤ f Y) :
    (∫ Y, f Y ∂firstEntranceWordMarkLaw D K x) ≤
      U * ∫ Y, f Y ∂referenceWordMarkLaw D K α := by
  rw [integral_referenceWordMark D K α hα hcap f hf,
    integral_firstEntranceWordMark D K x f hf, mul_add, Finset.mul_sum]
  apply add_le_add
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hzero (hn none)
  · apply Finset.sum_le_sum
    intro y hy
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hu y hy) (integral_nonneg hn)

/-- The full ordered-word event upper comparison includes the zero mark. -/
theorem firstEntranceWordMark_event_uniform_upper (D K : Finset Site) (x : Site)
    (α U : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (hzero : competingExitMass D K x ≤ U * (1 - α * capacity D K))
    (hu : ∀ y ∈ K, (competingEntranceLaw D K x).real {y} ≤
      U * (α * equilibriumMeasure D K y)) (s : Set WordMark) (hs : MeasurableSet s) :
    (firstEntranceWordMarkLaw D K x).real s ≤ U * (referenceWordMarkLaw D K α).real s := by
  have hn : ∀ Y, 0 ≤ s.indicator (fun _ : WordMark ↦ (1 : ℝ)) Y := by
    intro Y
    by_cases hY : Y ∈ s <;> simp [Set.indicator, hY]
  have h := firstEntranceWordMark_test_uniform_upper D K x α U hα hcap hzero hu
    (s.indicator (fun _ : WordMark ↦ (1 : ℝ)))
    (fun y _ ↦ (integrable_const (1 : ℝ)).indicator hs) hn
  have ha : (∫ Y, s.indicator (fun _ : WordMark ↦ (1 : ℝ)) Y
      ∂firstEntranceWordMarkLaw D K x) = (firstEntranceWordMarkLaw D K x).real s :=
    integral_indicator_one hs
  have hr : (∫ Y, s.indicator (fun _ : WordMark ↦ (1 : ℝ)) Y
      ∂referenceWordMarkLaw D K α) = (referenceWordMarkLaw D K α).real s :=
    integral_indicator_one hs
  rwa [ha, hr] at h

end SRWTightness
