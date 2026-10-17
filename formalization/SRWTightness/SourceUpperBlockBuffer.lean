import SRWTightness.SourceUpperBlockScales
import SRWTightness.SourceUpperMeshGrowth

open Filter

namespace SRWTightness

/-- The uniform source block buffer has the reciprocal-level size needed for sharp returns. -/
theorem source_upper_block_relative_buffer :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t →
      sourceUpperBuffer t ≤ sourceUpperTraversalRadius t (j + 1) /
        (200 * ((j : ℝ) + 1)) := by
  filter_upwards [source_upper_coarse_range_eventually,
    eventually_ge_atTop (max 2800 (Real.exp 1))] with t ht hlarge
  have ht2800 : 2800 ≤ t := (le_max_left _ _).trans hlarge
  have ht0 : 0 < t := by linarith
  have hlog : 1 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hlarge)
    simpa only [Real.log_exp] using h
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  have hr1 : 1 ≤ r := by
    change 1 ≤ (sourceUpperBlockSide t : ℝ)
    exact_mod_cast (show 1 ≤ sourceUpperBlockSide t from sourceUpperBlockSide_pos t)
  have hH : 0 ≤ sourceUpperBuffer t := by
    unfold sourceUpperBuffer
    change 0 ≤ 4 * r + 10
    linarith
  have hHbound : sourceUpperBuffer t ≤ 14 * r := by
    unfold sourceUpperBuffer
    dsimp [r]
    linarith
  have hf := source_upper_fine_ratio_bound t ht0 hlog
  have hm : 0 < sourceUpperRadius t := Real.exp_pos _
  have hquad : t ^ 2 * r ≤ sourceUpperRadius t := by
    have h := (div_le_div_iff₀ hm ht0).mp hf
    dsimp [r]
    nlinarith
  have h2800 : 2800 * t * r ≤ sourceUpperRadius t := by
    have h := mul_le_mul_of_nonneg_right
      (show 2800 * t ≤ t ^ 2 by nlinarith) (show 0 ≤ r by linarith)
    nlinarith
  have hell : 1 ≤ sourceRootDepth (Real.exp t) (sourceUpperRadius t) := by
    unfold sourceRootDepth
    rw [source_upper_root_log]
    exact (Nat.one_le_floor_iff _).mpr ht
  intro j hj
  have hjell : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceUpperRadius t) := by
    unfold sourceUpperCoarseDepth at hj
    omega
  have hrad := sourceRecordRadius_ge_terminal (sourceUpperRadius t) hm.le
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (j + 1) hjell
  change sourceUpperRadius t ≤ sourceUpperTraversalRadius t (j + 1) at hrad
  have hjt : (j : ℝ) + 1 ≤ t := by
    have hj' : (j : ℝ) ≤ sourceUpperCoarseDepth t := by exact_mod_cast hj
    have h := (source_upper_coarse_depth_error t ht).2
    have hD : 0 ≤ sourceUpperLogRadius t := by unfold sourceUpperLogRadius; positivity
    have hl : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  apply (le_div_iff₀ (by positivity : 0 < 200 * ((j : ℝ) + 1))).mpr
  have h₁ := mul_le_mul_of_nonneg_right hjt hH
  have h₂ := mul_le_mul_of_nonneg_left hHbound ht0.le
  nlinarith

end SRWTightness
