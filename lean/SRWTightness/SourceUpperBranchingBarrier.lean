import SRWTightness.GWUpperShiftedBarrier
import SRWTightness.SourceUpperBarrierDefinition

namespace SRWTightness

/-- The initial branching-barrier endpoint from source equation (4.25). -/
noncomputable def sourceUpperBranchingStart (t s : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  x + (4 + s) + sourceUpperSlope t s * k + 2 * (k : ℝ) ^ (1 / 4 : ℝ)

/-- The terminal branching-barrier endpoint from source equation (4.25). -/
noncomputable def sourceUpperBranchingEnd (t s : ℝ) : ℝ :=
  sourceUpperTarget t s + (4 + s) +
    2 * upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)

/-- The actual upper traversal barrier is dominated by the stated branching barrier. -/
theorem source_upper_branching_barrier (t s x : ℝ) (k j : ℕ)
    (hk : k < sourceUpperCoarseDepth t) (hj : j ≤ sourceUpperCoarseDepth t - k)
    (hx : 0 ≤ x) (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t)) :
    sourceUpperBarrier t s (k + j) ≤
      gwBarrierLine (sourceUpperBranchingStart t s k x) (sourceUpperBranchingEnd t s)
        j (sourceUpperCoarseDepth t - k) +
          gwBarrierCurvature (1 / 2 - 1 / 4) j (sourceUpperCoarseDepth t - k) := by
  have hh := gw_upper_shifted_barrier (sourceUpperCoarseDepth t - k) j (by omega) hj
    (sourceUpperSlope t s) (4 + s) x k (upperTerminalDepth (sourceUpperLogRadius t))
    hx (Nat.cast_nonneg _) hd
  have he : (k : ℝ) + (sourceUpperCoarseDepth t - k : ℕ) = sourceUpperCoarseDepth t := by
    rw [Nat.cast_sub hk.le]
    ring
  have hcurv : sourceUpperTotalDepth t - (k + j : ℕ) =
      (sourceUpperCoarseDepth t - k : ℕ) - (j : ℝ) +
        upperTerminalDepth (sourceUpperLogRadius t) := by
    unfold sourceUpperTotalDepth
    rw [Nat.cast_add, Nat.cast_sub hk.le]
    ring
  simp only [Nat.cast_add] at hcurv
  simpa only [sourceUpperBarrier, sourceUpperBarrierCurvature, sourceUpperBranchingStart,
    sourceUpperBranchingEnd, sourceUpperTarget, Nat.cast_add, he, hcurv] using hh

/-- A half-open source endpoint window is contained in the closed branching event. -/
theorem source_upper_branching_event_subset (t s x u : ℝ) (k : ℕ)
    (hk : k < sourceUpperCoarseDepth t) (hx : 0 ≤ x)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t)) :
    {r : GeometricGWRecord |
      (∀ j : ℕ, 0 < j → j < sourceUpperCoarseDepth t - k →
        geometricGWHeight r j ≤ sourceUpperBarrier t s (k + j)) ∧
      geometricGWHeight r (sourceUpperCoarseDepth t - k) ∈ Set.Ico u (u + 1)} ⊆
      gwUpperBarrierEvent (sourceUpperCoarseDepth t - k)
        (sourceUpperBranchingStart t s k x) (sourceUpperBranchingEnd t s) u 1 1 (1 / 4) := by
  intro r hr
  refine ⟨?_, hr.2.1, hr.2.2.le⟩
  intro j hj hJ
  simpa only [one_mul] using (hr.1 j hj hJ).trans
    (source_upper_branching_barrier t s x k j hk hJ.le hx hd)

end SRWTightness
