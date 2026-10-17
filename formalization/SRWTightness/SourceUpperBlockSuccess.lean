import SRWTightness.SourceUpperBlockVisits
import SRWTightness.SourceUpperBarrierDefinition
import SRWTightness.SourceUpperSlopeError

open Filter MeasureTheory

namespace SRWTightness

/-- The actual block high-local-time event below all later traversal barriers. -/
def sourceUpperBlockSuccess (t s : ℝ) (b : Site) : Set Sample :=
  {ω | (∃ y : sourceUpperBlock t b,
      sourceUpperVisitCutoff t s ≤ domainLocalTime (diskFinset (Real.exp t)) 0 y ω) ∧
    ∀ j : ℕ, sourceUpperBlockRoot t b < j → j ≤ sourceUpperCoarseDepth t →
      Real.sqrt (2 * (sourceUpperBlockCount t b j ω : ℝ)) ≤ sourceUpperBarrier t s j}

/-- The block success condition expressed entirely in finite forest records. -/
def sourceUpperForestSuccess (t s : ℝ) (b : Site) :
    Set (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b))) :=
  {rs | (∃ y : sourceUpperBlock t b, sourceUpperVisitCutoff t s ≤
      ((rs.flatMap (finiteRecordLeaves (sourceUpperBlockForestDepth t b))).map
        (fun v ↦ v y)).sum) ∧
    ∀ j : ℕ, sourceUpperBlockRoot t b < j → j ≤ sourceUpperCoarseDepth t →
      Real.sqrt (2 * (forestLevelPopulation (sourceUpperBlockForestDepth t b) rs
        (sourceRootDepth (Real.exp t) (sourceUpperRadius t) - (j + 1)) : ℝ)) ≤
          sourceUpperBarrier t s j}

/-- Actual block success is almost surely exactly its finite-record success event. -/
theorem source_upper_block_success_iff_ae :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t, ∀ᵐ ω ∂pathLaw,
      ∀ s : ℝ, ω ∈ sourceUpperBlockSuccess t s b ↔
        sourceUpperBlockForest t b (wordOccupationMark (sourceUpperBlock t b)) ω ∈
          sourceUpperForestSuccess t s b := by
  filter_upwards [source_upper_block_forest_mark_visits_ae,
    source_upper_block_root_lt_depth] with t hv hk
  intro b hb
  filter_upwards [hv b hb] with ω hω
  intro s
  have hc (j : ℕ) (hj : sourceUpperBlockRoot t b < j)
      (hJ : j ≤ sourceUpperCoarseDepth t) :=
    source_upper_block_forest_population t b (wordOccupationMark (sourceUpperBlock t b))
      ω j hj.le (by
        have := hk b hb
        change j ≤ sourceRootDepth (Real.exp t) (sourceUpperRadius t) - 1 at hJ
        omega)
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor
  · rintro ⟨⟨y, hy⟩, hbar⟩
    exact ⟨⟨y, by simpa only [hω y] using hy⟩,
      fun j hj hJ ↦ by simpa only [hc j hj hJ] using hbar j hj hJ⟩
  · rintro ⟨⟨y, hy⟩, hbar⟩
    exact ⟨⟨y, by simpa only [hω y] using hy⟩,
      fun j hj hJ ↦ by simpa only [hc j hj hJ] using hbar j hj hJ⟩

/-- The source cutoff is positive throughout its positive-time height range. -/
theorem source_upper_visit_cutoff_pos (t s : ℝ) (ht : 0 < t)
    (hs : 0 ≤ s) (hslog : s ≤ Real.log t) : 1 ≤ sourceUpperVisitCutoff t s := by
  have hy := ht.trans_le (source_upper_height_bounds t s ht hs hslog).1
  change 0 < Nat.ceil (sourceUpperHeight t s ^ 2 / Real.pi)
  exact Nat.ceil_pos.mpr (div_pos (sq_pos_of_pos hy) Real.pi_pos)

/-- Positive-threshold forest success cannot occur with zero roots. -/
theorem source_upper_forest_success_length_pos (t s : ℝ) (b : Site)
    (hcut : 1 ≤ sourceUpperVisitCutoff t s)
    (rs : List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b))) (hrs : rs ∈ sourceUpperForestSuccess t s b) :
    1 ≤ rs.length := by
  obtain ⟨⟨y, hy⟩, _⟩ := hrs
  by_contra h
  have he : rs = [] := List.length_eq_zero_iff.mp (by omega)
  simp only [he, List.flatMap_nil, List.map_nil, List.sum_nil] at hy
  omega

end SRWTightness
