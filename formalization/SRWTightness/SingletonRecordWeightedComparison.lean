import SRWTightness.EventWeightedComparison

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Single-root event domination controls every nonnegative weight on the selected record. -/
theorem singleton_record_lintegral_comparison {Ω R : Type*}
    [MeasurableSpace Ω] [Countable R] [MeasurableSpace R] [MeasurableSingletonClass R]
    [MeasurableSpace (List R)] [MeasurableSingletonClass (List R)]
    (μ : Measure Ω) (ν : Measure R) (F : Ω → List R) (hF : Measurable F)
    (S : Set R) (c : ℝ≥0∞)
    (hc : ∀ s : Set R, s ⊆ S → μ {ω | ∃ r ∈ s, F ω = [r]} ≤ c * ν s)
    (f : R → ℝ≥0∞) :
    (∫⁻ ω in F ⁻¹' ((fun r : R ↦ [r]) '' S), ((F ω).map f).sum ∂μ) ≤
      c * ∫⁻ r in S, f r ∂ν := by
  let embed : R → List R := fun r ↦ [r]
  let A : Set (List R) := embed '' S
  let g : List R → ℝ≥0∞ := fun rs ↦ (rs.map f).sum
  have he : Measurable embed := measurable_of_countable _
  have hA : MeasurableSet A := A.to_countable.measurableSet
  have hg : Measurable g := measurable_of_countable _
  have hbound : ∀ s : Set (List R), MeasurableSet s → s ⊆ A →
      μ (F ⁻¹' s) ≤ c * (ν.map embed) s := by
    intro s hs hsub
    have hS : embed ⁻¹' s ⊆ S := by
      intro r hr
      obtain ⟨r', hr', heq⟩ := hsub hr
      have heq' : r' = r := by simpa only [embed, List.cons.injEq, and_true] using heq
      simpa only [heq'] using hr'
    have hevent : F ⁻¹' s = {ω | ∃ r ∈ embed ⁻¹' s, F ω = [r]} := by
      ext ω
      constructor
      · intro hω
        obtain ⟨r, hr, heq⟩ := hsub hω
        exact ⟨r, by change embed r ∈ s; rw [heq]; exact hω, heq.symm⟩
      · rintro ⟨r, hr, heq⟩
        change F ω ∈ s
        rw [heq]
        exact hr
    rw [hevent, Measure.map_apply he hs]
    exact hc (embed ⁻¹' s) hS
  have hh := restricted_lintegral_le_of_event_comparison μ (ν.map embed) F hF A hA c
    hbound g hg
  rw [setLIntegral_map hA hg he] at hh
  have hpre : embed ⁻¹' A = S := by
    ext r
    simp [A, embed]
  rw [hpre] at hh
  simpa only [g, embed, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] using hh

end SRWTightness
