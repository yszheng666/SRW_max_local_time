import SRWTightness.OrderedWordCenteredIntegrals

open MeasureTheory
namespace SRWTightness

/-- Lower bounds for the empty atom and entrance weights control every nonnegative ordered test. -/
theorem firstEntranceWordMark_test_uniform_lower (D K : Finset Site) (x : Site)
    (α c : ℝ) (hα : 0 ≤ α) (hc : 0 ≤ c) (hcap : α * capacity D K ≤ 1)
    (hzero : c ≤ competingExitMass D K x)
    (hu : ∀ y ∈ K, c * (α * equilibriumMeasure D K y) ≤
      (competingEntranceLaw D K x).real {y})
    (f : WordMark → ℝ) (hf : ∀ y ∈ K, Integrable f (killedWordMarkLaw D y))
    (hn : ∀ Y, 0 ≤ f Y) :
    c * (∫ Y, f Y ∂referenceWordMarkLaw D K α) ≤
      ∫ Y, f Y ∂firstEntranceWordMarkLaw D K x := by
  rw [integral_referenceWordMark D K α hα hcap f hf,
    integral_firstEntranceWordMark D K x f hf, mul_add, Finset.mul_sum]
  apply add_le_add
  · have hz : c * (1 - α * capacity D K) ≤ competingExitMass D K x := by
      have hm : 1 - α * capacity D K ≤ 1 := by
        nlinarith [mul_nonneg hα (capacity_nonneg D K)]
      have hmul : c * (1 - α * capacity D K) ≤ c := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hm hc
      exact hmul.trans hzero
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hz (hn none)
  · apply Finset.sum_le_sum
    intro y hy
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hu y hy) (integral_nonneg hn)

/-- The same uniform lower bound applies to every measurable ordered-word event. -/
theorem firstEntranceWordMark_event_uniform_lower (D K : Finset Site) (x : Site)
    (α c : ℝ) (hα : 0 ≤ α) (hc : 0 ≤ c) (hcap : α * capacity D K ≤ 1)
    (hzero : c ≤ competingExitMass D K x)
    (hu : ∀ y ∈ K, c * (α * equilibriumMeasure D K y) ≤
      (competingEntranceLaw D K x).real {y}) (s : Set WordMark) (hs : MeasurableSet s) :
    c * (referenceWordMarkLaw D K α).real s ≤ (firstEntranceWordMarkLaw D K x).real s := by
  have hn : ∀ Y, 0 ≤ s.indicator (fun _ : WordMark ↦ (1 : ℝ)) Y := by
    intro Y
    by_cases hY : Y ∈ s <;> simp [Set.indicator, hY]
  have h := firstEntranceWordMark_test_uniform_lower D K x α c hα hc hcap hzero hu
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
