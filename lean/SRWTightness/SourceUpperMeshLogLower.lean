import SRWTightness.SourceUpperMeshGeometry
import SRWTightness.SourceUpperDepthError

namespace SRWTightness

/-- The actual root floor gives a sharp lower bound on the upper mesh logarithmic denominator. -/
theorem source_upper_mesh_log_lower (t : ℝ) (j : ℕ)
    (ht : 1 ≤ t - sourceUpperLogRadius t - Real.log 32)
    (hr : 10 ≤ sourceUpperTraversalRadius t (j + 1)) :
    (j : ℝ) + 1 + Real.log 32 ≤ Real.log (2 * Real.exp t /
      (sourceUpperTraversalRadius t (j + 1) + sourceUpperMeshBuffer t j)) := by
  let r := sourceUpperTraversalRadius t (j + 1)
  let H := sourceUpperMeshBuffer t j
  have hb := source_upper_mesh_buffer_bound t j hr
  have hr0 : 0 < r := by change 10 ≤ r at hr; linarith
  have hH : 0 ≤ H := hb.1
  have hhalf : 2 * H ≤ r := hb.2
  have hblog := Real.log_le_log (show 0 < r + H by linarith)
    (show r + H ≤ 2 * r by linarith)
  have hell : (sourceRootDepth (Real.exp t) (sourceUpperRadius t) : ℝ) ≤
      t - sourceUpperLogRadius t - Real.log 32 := by
    unfold sourceRootDepth
    rw [source_upper_root_log]
    exact Nat.floor_le (by linarith)
  have hlr : Real.log r = sourceUpperLogRadius t +
      (sourceRootDepth (Real.exp t) (sourceUpperRadius t) : ℝ) - ((j : ℝ) + 1) := by
    dsimp only [r, sourceUpperTraversalRadius, sourceRecordRadius]
    have hm : sourceUpperRadius t ≠ 0 := Real.exp_ne_zero _
    rw [Real.log_mul hm (Real.exp_ne_zero _), Real.log_exp]
    rw [sourceUpperRadius, Real.log_exp]
    push_cast
    ring
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hr0.ne', hlr] at hblog
  change (j : ℝ) + 1 + Real.log 32 ≤ Real.log (2 * Real.exp t / (r + H))
  rw [Real.log_div (by positivity) (by linarith),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  linarith

end SRWTightness
