import SRWTightness.SourceDeficitBand
import SRWTightness.SourceRootDepth
import SRWTightness.SourceExcursionDomains

open Filter

namespace SRWTightness

/-- The manuscript outer radius eventually contains at least one full root generation. -/
theorem source_outer_scale_large :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      sourceScaleThreshold 4 ≤ t ∧ 32 * Real.exp 1 * sourceLowerRadius t ≤ Real.exp t := by
  have hh : ∀ᶠ t : ℝ in atTop,
      sourceScaleThreshold 4 ≤ t ∧
        32 * Real.exp 1 * sourceLowerRadius t ≤ Real.exp t := by
    filter_upwards [source_deficit_large_conditions,
      eventually_ge_atTop (2 * (Real.log 32 + 1 + sourceLowerTimeError))] with t ht hbig
    have hm := sourceLowerRadius_pos t
    have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).2.2.1
    have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
    have hlog := (abs_le.mp (sourceLowerTime_log_bound (sourceLowerRadius t)
      (by linarith))).1
    have he := Real.exp_le_exp.mpr
      (show Real.log 32 + 1 + Real.log (sourceLowerRadius t) ≤ t by linarith [ht.2.2.1])
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 32),
      Real.exp_log hm] at he
    exact ⟨ht.1, he⟩
  exact eventually_atTop.mp hh

/-- Centers in the manuscript annulus satisfy both actual root geometric conditions. -/
theorem source_annular_center_geometry (R m : ℝ) (hm : 70 ≤ m) (hscale : 32 * m ≤ R)
    (b : Site) (hblo : R / 4 ≤ Real.sqrt (normSq b))
    (hbhi : Real.sqrt (normSq b) ≤ R / 3) (k : ℕ) :
    sourceRecordRadius m (sourceRootDepth R m) (k + 1) - 14 ≤ Real.sqrt (normSq b) ∧
      Real.sqrt (normSq b) + (sourceRecordRadius m (sourceRootDepth R m) k + 14) + 1 < R := by
  have hbr := (source_root_depth_bracket R m (by linarith) hscale).1
  have hchild := sourceRecordRadius_antitone m (by linarith)
    (sourceRootDepth R m) (Nat.zero_le (k + 1))
  have hroot := sourceRecordRadius_antitone m (by linarith)
    (sourceRootDepth R m) (Nat.zero_le k)
  constructor <;> linarith

/-- The large outer scale ensures that the level-zero root exists. -/
theorem source_root_depth_pos (R m : ℝ) (hm : 0 < m)
    (hscale : 32 * Real.exp 1 * m ≤ R) : 0 < sourceRootDepth R m := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbase : 32 * m ≤ R := by nlinarith
  have hh := (source_root_depth_bracket R m hm hbase).2
  by_contra hn
  have hz : sourceRootDepth R m = 0 := by omega
  simp only [hz, sourceRecordRadius, Nat.cast_zero, sub_self, Real.exp_zero, mul_one] at hh
  linarith

end SRWTightness
