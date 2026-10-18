import SRWTightness.SourceUpperThresholdConditions

open Filter
open scoped Topology
namespace SRWTightness

/-- Curvature of the source upper traversal barrier in equation (4.12). -/
noncomputable def sourceUpperBarrierCurvature (t : ℝ) (j : ℕ) : ℝ :=
  (min (j : ℝ) (sourceUpperTotalDepth t - j)) ^ (1 / 4 : ℝ)

/-- The source upper traversal barrier, with its full dependence on the excess height. -/
noncomputable def sourceUpperBarrier (t s : ℝ) (j : ℕ) : ℝ :=
  sourceUpperSlope t s * j + (4 + s) + sourceUpperBarrierCurvature t j

/-- At the terminal generation the smaller curvature argument is the terminal Green depth. -/
theorem source_upper_barrier_terminal_curvature (t : ℝ)
    (hd : upperTerminalDepth (sourceUpperLogRadius t) ≤ (sourceUpperCoarseDepth t : ℝ)) :
    sourceUpperBarrierCurvature t (sourceUpperCoarseDepth t) =
      upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) := by
  unfold sourceUpperBarrierCurvature sourceUpperTotalDepth
  rw [add_sub_cancel_left, min_eq_right hd]

/-- The actual source scales eventually place the terminal Green depth below the coarse depth. -/
theorem source_upper_terminal_depth_le_coarse (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop,
      upperTerminalDepth (sourceUpperLogRadius t) ≤ (sourceUpperCoarseDepth t : ℝ) := by
  obtain ⟨B, _, hcond⟩ := source_upper_threshold_conditions hScale
  have hsmall := (source_upper_depth_log_power_limit hScale 0).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hcond, hsmall] with t ht hs
  simp only [pow_zero, mul_one] at hs
  have hd := (div_lt_iff₀ ht.1).mp hs
  have htotal := ht.2.2.2.1
  unfold sourceUpperTotalDepth at htotal
  linarith

/-- The endpoint identity following equation (4.12), uniformly for every excess height. -/
theorem source_upper_barrier_terminal (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ,
      sourceUpperBarrier t s (sourceUpperCoarseDepth t) =
        sourceUpperTarget t s + (4 + s) +
          upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) := by
  filter_upwards [source_upper_terminal_depth_le_coarse hScale] with t ht
  intro s
  unfold sourceUpperBarrier sourceUpperTarget
  rw [source_upper_barrier_terminal_curvature t ht]

end SRWTightness
