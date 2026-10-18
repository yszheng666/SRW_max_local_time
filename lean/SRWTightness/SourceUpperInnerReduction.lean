import SRWTightness.SourceUpperNearOriginSourceEvent
import SRWTightness.SourceUpperAnnulusReduction

open Filter MeasureTheory

namespace SRWTightness

open scoped Classical

/-- A high local-time point in the open half-radius disk of the actual killed walk. -/
def sourceUpperInnerHighEvent (t s : ℝ) : Set Sample :=
  {ω | ∃ x ∈ diskFinset (Real.exp t / 2), sourceUpperVisitCutoff t s ≤
    domainLocalTime (diskFinset (Real.exp t)) 0 x ω}

/-- Every inner high point lies either in the closed near-origin region or in the annulus. -/
theorem source_upper_inner_split (t s : ℝ) :
    sourceUpperInnerHighEvent t s ⊆
      sourceUpperNearOriginHighEvent t s ∪ sourceUpperAnnulusHighEvent t s := by
  intro ω hω
  obtain ⟨x, hx, hhigh⟩ := hω
  by_cases hn : Real.sqrt (normSq x) ≤ Real.exp t / t
  · left
    refine ⟨x, ?_, hhigh⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hn⟩
    exact diskFinset_mono _ _ (by positivity) (by linarith [Real.exp_pos t]) hx
  · right
    exact ⟨x, hx, lt_of_not_ge hn, hhigh⟩

/-- The actual inner-disk probability is bounded by the near-origin and annulus probabilities. -/
theorem source_upper_inner_probability_split (t s : ℝ) :
    pathLaw.real (sourceUpperInnerHighEvent t s) ≤
      pathLaw.real (sourceUpperNearOriginHighEvent t s) +
        pathLaw.real (sourceUpperAnnulusHighEvent t s) := by
  apply (measureReal_mono (source_upper_inner_split t s) (measure_ne_top _ _)).trans
  exact measureReal_union_le _ _

/-- The source inner event reduces to the near-origin region, crossings and actual block successes. -/
theorem source_upper_inner_success_reduction (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
      ω ∈ sourceUpperInnerHighEvent t s →
        ω ∈ sourceUpperNearOriginHighEvent t s ∨ ω ∈ sourceUpperCrossingEvent t s ∨
          ∃ b ∈ sourceUpperBlockCenters t, ω ∈ sourceUpperBlockSuccess t s b := by
  filter_upwards [source_upper_annulus_success_reduction hF] with t ht
  filter_upwards [ht] with ω hω
  intro s hs
  rcases source_upper_inner_split t s hs with hn | ha
  · exact Or.inl hn
  · exact Or.inr (hω s ha)

/-- Open-disk form of source (4.36): the inner high-event indicator is dominated by the three actual contributions. -/
theorem source_upper_inner_indicator_reduction (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
      (if ω ∈ sourceUpperInnerHighEvent t s then (1 : ℝ) else 0) ≤
        (if ω ∈ sourceUpperNearOriginHighEvent t s then (1 : ℝ) else 0) +
        (if ω ∈ sourceUpperCrossingEvent t s then (1 : ℝ) else 0) +
        ∑ b ∈ sourceUpperBlockCenters t,
          (if ω ∈ sourceUpperBlockSuccess t s b then (1 : ℝ) else 0) := by
  classical
  filter_upwards [source_upper_inner_success_reduction hF] with t ht
  filter_upwards [ht] with ω hω
  intro s
  have hsum : 0 ≤ ∑ b ∈ sourceUpperBlockCenters t,
      (if ω ∈ sourceUpperBlockSuccess t s b then (1 : ℝ) else 0) :=
    Finset.sum_nonneg (fun _ _ ↦ by positivity)
  by_cases hi : ω ∈ sourceUpperInnerHighEvent t s
  · rcases hω s hi with hn | hc | ⟨b, hb, hsucc⟩
    · simp only [if_pos hi, if_pos hn]
      split_ifs <;> linarith
    · simp only [if_pos hi, if_pos hc]
      split_ifs <;> linarith
    · have hh := Finset.single_le_sum
        (fun a (_ : a ∈ sourceUpperBlockCenters t) ↦
          show 0 ≤ (if ω ∈ sourceUpperBlockSuccess t s a then (1 : ℝ) else 0) by positivity) hb
      simp only [if_pos hsucc] at hh
      simp only [if_pos hi]
      split_ifs <;> linarith
  · simp only [if_neg hi]
    split_ifs <;> linarith

end SRWTightness
