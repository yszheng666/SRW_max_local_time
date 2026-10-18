import SRWTightness.SourceUpperDirectIndicator

open Filter MeasureTheory
open scoped Classical

namespace SRWTightness

/-- Closed half-radius high event with the original integer local-time cutoff. -/
def sourceUpperClosedCutoffEvent (t s : ℝ) : Set Sample :=
  {ω | ∃ x : Site, Real.sqrt (normSq x) ≤ Real.exp t / 2 ∧
    sourceUpperVisitCutoff t s ≤ domainLocalTime (diskFinset (Real.exp t)) 0 x ω}

/-- High points on the half-radius boundary omitted by the existing open crossing convention. -/
def sourceUpperBoundaryCutoffEvent (t s : ℝ) : Set Sample :=
  {ω | ∃ x : Site, Real.sqrt (normSq x) = Real.exp t / 2 ∧
    sourceUpperVisitCutoff t s ≤ domainLocalTime (diskFinset (Real.exp t)) 0 x ω}

/-- The closed event decomposes into the open event and its exact boundary event. -/
theorem source_upper_closed_cutoff_split (t s : ℝ) :
    sourceUpperClosedCutoffEvent t s =
      sourceUpperInnerHighEvent t s ∪ sourceUpperBoundaryCutoffEvent t s := by
  ext ω
  constructor
  · rintro ⟨x, hx, hh⟩
    by_cases hlt : Real.sqrt (normSq x) < Real.exp t / 2
    · left
      refine ⟨x, ?_, hh⟩
      exact (mem_diskFinset _ _).mpr ((Real.sqrt_lt (normSq_nonneg x) (by positivity)).mp hlt)
    · right
      exact ⟨x, le_antisymm hx (le_of_not_gt hlt), hh⟩
  · rintro (⟨x, hx, hh⟩ | ⟨x, hx, hh⟩)
    · refine ⟨x, ?_, hh⟩
      exact ((Real.sqrt_lt (normSq_nonneg x) (by positivity)).mpr
        ((mem_diskFinset _ _).mp hx)).le
    · exact ⟨x, hx.le, hh⟩

/-- With the source's open crossing event, the closed indicator has an explicit boundary correction. -/
theorem source_upper_closed_direct_indicator_with_boundary (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
      (if ω ∈ sourceUpperClosedCutoffEvent t s then (1 : ℝ) else 0) ≤
        (if ω ∈ sourceUpperNearOriginHighEvent t s then (1 : ℝ) else 0) +
        (if ω ∈ sourceUpperCrossingEvent t s then (1 : ℝ) else 0) +
        (∑ b ∈ sourceUpperBlockCenters t,
          (if ω ∈ sourceUpperDirectBlockSuccess t s b then (1 : ℝ) else 0)) +
        (if ω ∈ sourceUpperBoundaryCutoffEvent t s then (1 : ℝ) else 0) := by
  filter_upwards [source_upper_open_direct_indicator hF] with t ht
  filter_upwards [ht] with ω hω
  intro s
  have hpoint : (if ω ∈ sourceUpperClosedCutoffEvent t s then (1 : ℝ) else 0) ≤
      (if ω ∈ sourceUpperInnerHighEvent t s then (1 : ℝ) else 0) +
      (if ω ∈ sourceUpperBoundaryCutoffEvent t s then (1 : ℝ) else 0) := by
    rw [source_upper_closed_cutoff_split]
    by_cases ho : ω ∈ sourceUpperInnerHighEvent t s <;>
      by_cases hb : ω ∈ sourceUpperBoundaryCutoffEvent t s <;> simp [ho, hb]
  exact hpoint.trans (add_le_add (hω s) le_rfl)

/-- At a boundary-free radius, the corrected inequality becomes the literal three-term inequality. -/
theorem source_upper_closed_direct_indicator_boundary_free (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, (∀ x : Site, Real.sqrt (normSq x) ≠ Real.exp t / 2) →
      ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
        (if ω ∈ sourceUpperClosedCutoffEvent t s then (1 : ℝ) else 0) ≤
          (if ω ∈ sourceUpperNearOriginHighEvent t s then (1 : ℝ) else 0) +
          (if ω ∈ sourceUpperCrossingEvent t s then (1 : ℝ) else 0) +
          ∑ b ∈ sourceUpperBlockCenters t,
            (if ω ∈ sourceUpperDirectBlockSuccess t s b then (1 : ℝ) else 0) := by
  filter_upwards [source_upper_closed_direct_indicator_with_boundary hF] with t ht
  intro hfree
  filter_upwards [ht] with ω hω
  intro s
  have hn : ω ∉ sourceUpperBoundaryCutoffEvent t s := by
    rintro ⟨x, hx, _⟩
    exact hfree x hx
  simpa only [if_neg hn, add_zero] using hω s

end SRWTightness
