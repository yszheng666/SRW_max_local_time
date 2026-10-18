import SRWTightness.SourceUpperBoundaryIndicator

open Filter MeasureTheory
open scoped Classical

namespace SRWTightness

/-- Exact original-radius form of the closed integer-cutoff event. -/
theorem source_upper_closed_cutoff_at_radius (R s : ℝ) (hR : 0 < R) :
    sourceUpperClosedCutoffEvent (Real.log R) s =
      {ω | ∃ x : Site, Real.sqrt (normSq x) ≤ R / 2 ∧
        Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x} := by
  ext ω
  simp only [sourceUpperClosedCutoffEvent, Set.mem_setOf_eq, Real.exp_log hR,
    sourceUpperVisitCutoff_at_radius, domainLocalTime_disk]

/-- Exact original-radius form of the omitted boundary high-point event. -/
theorem source_upper_boundary_cutoff_at_radius (R s : ℝ) (hR : 0 < R) :
    sourceUpperBoundaryCutoffEvent (Real.log R) s =
      {ω | ∃ x : Site, Real.sqrt (normSq x) = R / 2 ∧
        Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x} := by
  ext ω
  simp only [sourceUpperBoundaryCutoffEvent, Set.mem_setOf_eq, Real.exp_log hR,
    sourceUpperVisitCutoff_at_radius, domainLocalTime_disk]

/-- Corrected source-radius indicator formula with its explicit boundary term and actual direct traversals. -/
theorem source_upper_indicator_radius_with_boundary (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ R : ℝ in atTop, ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
      (if (∃ x : Site, Real.sqrt (normSq x) ≤ R / 2 ∧
        Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x) then (1 : ℝ) else 0) ≤
      (if (∃ x : Site, Real.sqrt (normSq x) ≤ R / Real.log R ∧
        Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x) then (1 : ℝ) else 0) +
      (if ω ∈ sourceUpperCrossingEvent (Real.log R) s then (1 : ℝ) else 0) +
      (∑ b ∈ sourceUpperBlockCenters (Real.log R),
        (if ω ∈ sourceUpperDirectBlockSuccess (Real.log R) s b then (1 : ℝ) else 0)) +
      (if (∃ x : Site, Real.sqrt (normSq x) = R / 2 ∧
        Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x) then (1 : ℝ) else 0) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (source_upper_closed_direct_indicator_with_boundary hF), eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 2)] with R ht hR hlog
  filter_upwards [ht] with ω hω
  intro s
  have hh := hω s
  rw [source_upper_closed_cutoff_at_radius R s hR,
    source_upper_near_origin_event_at_radius R s hR hlog,
    source_upper_boundary_cutoff_at_radius R s hR] at hh
  exact hh

/-- The literal source three-term formula holds at every sufficiently large boundary-free radius. -/
theorem source_upper_indicator_radius_boundary_free (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ R : ℝ in atTop, (∀ x : Site, Real.sqrt (normSq x) ≠ R / 2) →
      ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
        (if (∃ x : Site, Real.sqrt (normSq x) ≤ R / 2 ∧
          Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x) then (1 : ℝ) else 0) ≤
        (if (∃ x : Site, Real.sqrt (normSq x) ≤ R / Real.log R ∧
          Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x) then (1 : ℝ) else 0) +
        (if ω ∈ sourceUpperCrossingEvent (Real.log R) s then (1 : ℝ) else 0) +
        ∑ b ∈ sourceUpperBlockCenters (Real.log R),
          (if ω ∈ sourceUpperDirectBlockSuccess (Real.log R) s b then (1 : ℝ) else 0) := by
  filter_upwards [source_upper_indicator_radius_with_boundary hF] with R ht
  intro hfree
  filter_upwards [ht] with ω hω
  intro s
  have hn : ¬ ∃ x : Site, Real.sqrt (normSq x) = R / 2 ∧
      Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x := by
    rintro ⟨x, hx, _⟩
    exact hfree x hx
  simpa only [if_neg hn, add_zero] using hω s

end SRWTightness
