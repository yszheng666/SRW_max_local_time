import SRWTightness.SourceEquilibriumTime
import SRWTightness.TerminalCutoffGeometry
import SRWTightness.GeometricDiskWeightBounds

namespace SRWTightness

/-- The terminal-time estimate v_I=6log(t)+O(1), at the exact maximal geometric scale. -/
theorem source_terminal_energy_bound (b : Site) (m t A q H : ℝ) (hm : 0 < m)
    (ht : 2 ≤ t) (hA : 1 ≤ A) (hq : 1 < q) (hcut : A ≤ m / t ^ 6)
    (hH : 0 ≤ H) (hHm : 5 * H ≤ m) :
    let I := geometricTerminalIndex A q (m / t ^ 6) (by linarith) hq hcut
    |sourceEquilibriumTime b m (A * q ^ I) H - 6 * Real.log t| ≤
      sourceEquilibriumTimeError + Real.log q := by
  have hA0 : 0 < A := by linarith
  let I := geometricTerminalIndex A q (m / t ^ 6) hA0 hq hcut
  have ha := geometric_radius_ge A q hA0.le hq.le I
  have hma := source_terminal_radius_separation m t A q ht hA0 hq hcut I le_rfl
  have hv := sourceEquilibriumTime_log_bound b m (A * q ^ I) H (by linarith) hma hH hHm
  have hl := source_terminal_log_bounds m t A q hm (by linarith) hA0 hq hcut
  have hlog : |Real.log m - Real.log (A * q ^ I) - 6 * Real.log t| ≤ Real.log q := by
    rw [abs_of_nonneg hl.1]
    exact hl.2
  have he : sourceEquilibriumTime b m (A * q ^ I) H - 6 * Real.log t =
      (sourceEquilibriumTime b m (A * q ^ I) H - (Real.log m - Real.log (A * q ^ I))) +
      (Real.log m - Real.log (A * q ^ I) - 6 * Real.log t) := by ring
  change |sourceEquilibriumTime b m (A * q ^ I) H - 6 * Real.log t| ≤ _
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hv hlog)

/-- The number of geometric scales is bounded using the original d, with no unproved asymptotic input. -/
theorem source_terminal_index_bound (m t A q : ℝ) (hm : 2 ≤ m) (ht : 2 ≤ t)
    (hA : 1 ≤ A) (hq : 1 < q) (hcut : A ≤ m / t ^ 6) :
    (geometricTerminalIndex A q (m / t ^ 6) (by linarith) hq hcut : ℝ) ≤
      (sourceLowerTime m + sourceLowerTimeError) / Real.log q := by
  have hA0 : 0 < A := by linarith
  have ht0 : 0 < t := by linarith
  have hm0 : 0 < m := by linarith
  have hi := geometricTerminalIndex_log_size A q (m / t ^ 6) hA0 hq hcut
  have hpow : 1 ≤ t ^ 6 := one_le_pow₀ (by linarith)
  have hLm : m / t ^ 6 ≤ m := by
    apply (div_le_iff₀ (by positivity : 0 < t ^ 6)).mpr
    nlinarith
  have hl := Real.log_le_log (by positivity : 0 < m / t ^ 6) hLm
  have hla := Real.log_nonneg hA
  have hd := (abs_le.mp (sourceLowerTime_log_bound m hm)).1
  apply hi.trans
  apply div_le_div_of_nonneg_right _ (Real.log_pos hq).le
  linarith

/-- An explicit linear-in-d version of the I=O(d) estimate. -/
theorem source_terminal_index_linear_bound (m t A q : ℝ) (hm : 2 ≤ m) (ht : 2 ≤ t)
    (hA : 1 ≤ A) (hq : 1 < q) (hcut : A ≤ m / t ^ 6) (hd : 1 ≤ sourceLowerTime m) :
    (geometricTerminalIndex A q (m / t ^ 6) (by linarith) hq hcut : ℝ) ≤
      ((1 + sourceLowerTimeError) / Real.log q) * sourceLowerTime m := by
  apply (source_terminal_index_bound m t A q hm ht hA hq hcut).trans
  have hE := sourceLowerTimeError_pos
  have hh : sourceLowerTime m + sourceLowerTimeError ≤
      (1 + sourceLowerTimeError) * sourceLowerTime m := by nlinarith
  have hb := div_le_div_of_nonneg_right hh (Real.log_pos hq).le
  convert hb using 1 <;> ring

end SRWTightness
