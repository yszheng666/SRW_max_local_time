import SRWTightness.SourceUpperMarkParameters

namespace SRWTightness

/-- Exact logarithm entering the coarse natural floor. -/
theorem source_upper_root_log (t : ℝ) :
    Real.log (Real.exp t / (32 * sourceUpperRadius t)) =
      t - sourceUpperLogRadius t - Real.log 32 := by
  unfold sourceUpperRadius
  rw [Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_mul (by norm_num : (32 : ℝ) ≠ 0)
      (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
  ring

/-- The natural coarse depth has the exact two-unit floor error in its admissible range. -/
theorem source_upper_coarse_depth_error (t : ℝ)
    (ht : 1 ≤ t - sourceUpperLogRadius t - Real.log 32) :
    -2 ≤ (sourceUpperCoarseDepth t : ℝ) -
      (t - sourceUpperLogRadius t - Real.log 32) ∧
    (sourceUpperCoarseDepth t : ℝ) -
      (t - sourceUpperLogRadius t - Real.log 32) ≤ -1 := by
  have hn : 1 ≤ sourceRootDepth (Real.exp t) (sourceUpperRadius t) := by
    unfold sourceRootDepth
    rw [source_upper_root_log]
    exact (Nat.one_le_floor_iff _).mpr ht
  have hl := Nat.floor_le (show 0 ≤ t - sourceUpperLogRadius t - Real.log 32 by linarith)
  have hu := Nat.lt_floor_add_one (t - sourceUpperLogRadius t - Real.log 32)
  unfold sourceUpperCoarseDepth
  rw [Nat.cast_sub hn, Nat.cast_one]
  unfold sourceRootDepth
  rw [source_upper_root_log]
  constructor <;> linarith

/-- A bounded terminal-depth error gives a bounded total-depth error, including the floor. -/
theorem source_upper_total_depth_error (t B : ℝ)
    (ht : 1 ≤ t - sourceUpperLogRadius t - Real.log 32)
    (hd : |upperTerminalDepth (sourceUpperLogRadius t) - sourceUpperLogRadius t| ≤ B) :
    |sourceUpperTotalDepth t - t| ≤ B + Real.log 32 + 2 := by
  have hn := source_upper_coarse_depth_error t ht
  have hd' := abs_le.mp hd
  have hlog : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  unfold sourceUpperTotalDepth
  apply abs_le.mpr
  constructor <;> linarith

/-- The proved Green estimate and the elementary radius error bound the terminal depth. -/
theorem source_upper_terminal_depth_error (u : ℝ) (hR : 2 ≤ upperTerminalRadius u)
    (hlog : |Real.log (upperTerminalRadius u) - u| ≤ 2) :
    |upperTerminalDepth u - u| ≤ diskGreenEnergyConstant / (2 / Real.pi) + 2 := by
  have hg := disk_normalized_reference_log_bound (upperTerminalRadius u) hR
  change |upperTerminalDepth u - Real.log (upperTerminalRadius u)| ≤ _ at hg
  exact (abs_sub_le _ _ _).trans (add_le_add hg hlog)

end SRWTightness
