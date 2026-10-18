import SRWTightness.SourceUpperBlockSuccess
import SRWTightness.SourceUpperBranchingDepth
import SRWTightness.SourceForestContinuationCoordinates

namespace SRWTightness

/-- The full upper barrier band, including the terminal generation. -/
def sourceUpperGWBand (t s : ℝ) (k n : ℕ) : Set GeometricGWRecord :=
  {g | ∀ j : ℕ, 0 < j → j ≤ n → geometricGWHeight g j ≤ sourceUpperBarrier t s (k + j)}

/-- High total occupation in a list of independent upper-block terminal marks. -/
def sourceUpperMarkListHighEvent (t s : ℝ) (b : Site) : Set (List (Mark (sourceUpperBlock t b))) :=
  {vs | ∃ y : sourceUpperBlock t b, sourceUpperVisitCutoff t s ≤ (vs.map (fun v ↦ v y)).sum}

/-- Forward manuscript levels and chronological GW levels read the same forest populations. -/
theorem source_upper_forest_gw_height (t : ℝ) (b : Site)
    (rs : List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b))) (j : ℕ)
    (hkj : sourceUpperBlockRoot t b ≤ j) (hj : j ≤ sourceUpperCoarseDepth t) :
    geometricGWHeight (forestPopulationList (sourceUpperBlockForestDepth t b) rs)
      (j - sourceUpperBlockRoot t b) =
        Real.sqrt (2 * (forestLevelPopulation (sourceUpperBlockForestDepth t b) rs
          (sourceRootDepth (Real.exp t) (sourceUpperRadius t) - (j + 1)) : ℝ)) := by
  have hn := sourceUpperBlockForestDepth_eq_remaining t b
  have hl : j - sourceUpperBlockRoot t b ≤ sourceUpperBlockForestDepth t b := by omega
  have hi : sourceUpperBlockForestDepth t b - (j - sourceUpperBlockRoot t b) =
      sourceRootDepth (Real.exp t) (sourceUpperRadius t) - (j + 1) := by
    unfold sourceUpperBlockForestDepth sourceUpperCoarseDepth at *
    omega
  unfold geometricGWHeight
  rw [forest_gw_population _ _ _ hl, hi]

/-- The actual forest success predicate is the joint GW-band and terminal-mark predicate. -/
theorem source_upper_forest_success_iff_joint (t s : ℝ) (b : Site)
    (hk : sourceUpperBlockRoot t b ≤ sourceUpperCoarseDepth t)
    (rs : List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b))) :
    rs ∈ sourceUpperForestSuccess t s b ↔
      forestPopulationList (sourceUpperBlockForestDepth t b) rs ∈
        sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b) ∧
      rs.flatMap (finiteRecordLeaves (sourceUpperBlockForestDepth t b)) ∈
        sourceUpperMarkListHighEvent t s b := by
  have hn := sourceUpperBlockForestDepth_eq_remaining t b
  constructor
  · intro hr
    refine ⟨?_, hr.1⟩
    intro l hl hln
    have hj : sourceUpperBlockRoot t b + l ≤ sourceUpperCoarseDepth t := by omega
    have hh := hr.2 (sourceUpperBlockRoot t b + l) (by omega) hj
    rw [← source_upper_forest_gw_height t b rs _ (by omega) hj] at hh
    simpa only [Nat.add_sub_cancel_left] using hh
  · rintro ⟨hband, hmarks⟩
    refine ⟨hmarks, ?_⟩
    intro j hj hJ
    have hl : j - sourceUpperBlockRoot t b ≤ sourceUpperBlockForestDepth t b := by omega
    have hh := hband (j - sourceUpperBlockRoot t b) (by omega) hl
    rw [source_upper_forest_gw_height t b rs j hj.le hJ] at hh
    simpa only [Nat.add_sub_of_le hj.le] using hh

end SRWTightness
