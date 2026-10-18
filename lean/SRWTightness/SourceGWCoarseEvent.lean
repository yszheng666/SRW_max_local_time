import SRWTightness.SourceGWActualLowerTubeProbability
import SRWTightness.GWTubeContainment

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- Full source coarse barrier, including the terminal layer and its half-open window. -/
def sourceGWCoarseWindowEvent (t : ℝ) (L : ℕ) (q : ℝ) : Set GeometricGWRecord :=
  {r | (∀ j : ℕ, 0 < j → j ≤ L → geometricGWHeight r j ≤
      4 + sourceBarrierSlope t * j -
        (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)) ∧
    geometricGWHeight r L ∈ Set.Ico (sourceTerminalRoot t q) (sourceTerminalRoot t q + 1)}

theorem sourceGWCoarseWindowEvent_measurable (t : ℝ) (L : ℕ) (q : ℝ) :
    MeasurableSet (sourceGWCoarseWindowEvent t L q) := Set.to_countable _ |>.measurableSet

/-- The actual lower tube is contained in the full coarse-window event, including its last layer. -/
theorem source_gw_lower_tube_subset :
    ∀ᶠ t : ℝ in atTop,
      let L := (sourceCoarseGeneration t).toNat
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        sourceGWLowerTubeEvent t L q ⊆ sourceGWCoarseWindowEvent t L q := by
  filter_upwards [source_deficit_large_conditions, source_gw_curvature_small,
    source_gw_natural_generation] with t ht hcurve hNat
  obtain ⟨ht, htE, hdsmall, hlog⟩ := ht
  have hd := sourceLowerTime_ge_one t ht
  have hT := sourceTotalTime_ge_half t ht htE
  unfold sourceTotalTime at hT
  have hN : sourceLowerTime (sourceLowerRadius t) ≤ (sourceCoarseGeneration t : ℝ) := by
    linarith
  let L := (sourceCoarseGeneration t).toNat
  have hL : (L : ℝ) = (sourceCoarseGeneration t : ℝ) := hNat.1
  have htime : (L : ℝ) + sourceLowerTime (sourceLowerRadius t) = sourceTotalTime t := by
    unfold sourceTotalTime
    rw [hL]
  have hendtime : sourceTotalTime t - (L : ℝ) = sourceLowerTime (sourceLowerRadius t) := by
    rw [← htime]
    ring
  dsimp only
  intro q hql hqu r hr
  have hr' : r ∈ gwTubeEvent L (Real.sqrt 2) (sourceTerminalRoot t q + 1 / 4) 4
      (sourceGWLowerEndpoint t) (1 / 2) 1 10 (1 / 10) := hr
  have he : sourceTerminalRoot t q + 1 / 4 + 1 / 2 = sourceTerminalRoot t q + 3 / 4 := by ring
  have hend : geometricGWHeight r L ∈
      Set.Icc (sourceTerminalRoot t q + 1 / 4) (sourceTerminalRoot t q + 3 / 4) := by
    simpa only [he] using hr'.2
  refine ⟨?_, gw_terminal_subwindow_subset _ hend⟩
  intro j hj hjL
  by_cases hjlast : j = L
  · subst j
    rw [hendtime, min_eq_right (show sourceLowerTime (sourceLowerRadius t) ≤ (L : ℝ) by
      rw [hL]; exact hN), hL]
    have hh := hend.2
    unfold sourceTerminalRoot at hh
    have hs0 := Real.sqrt_nonneg (sourceLowerTime (sourceLowerRadius t))
    nlinarith
  · have hjlt : j < L := by omega
    have hh := (hr'.1 j hj hjlt).2
    simp only [one_mul] at hh
    have hc := gw_source_tube_upper_le_barrier L j hNat.2 hjL
      (sourceBarrierSlope t) (sourceLowerTime (sourceLowerRadius t)) (by linarith)
    rw [htime] at hc
    have hb : 4 + sourceBarrierSlope t * L -
        2 * sourceLowerTime (sourceLowerRadius t) ^ (2 / 5 : ℝ) = sourceGWLowerEndpoint t := by
      unfold sourceGWLowerEndpoint
      rw [hL]
    rw [hb] at hc
    exact hh.trans hc

end SRWTightness
