import SRWTightness.SourceUpperMeshScale

open Filter

namespace SRWTightness

/-- The exact exponential upper radius dominates t squared in the logarithmic regime. -/
theorem source_upper_radius_ge_sq (t : ℝ) (ht : 0 < t) (hlog : 1 ≤ Real.log t) :
    t ^ 2 ≤ sourceUpperRadius t := by
  have hp : Real.log t ≤ (Real.log t) ^ 4 := by
    nlinarith [sq_nonneg (Real.log t - 1), sq_nonneg ((Real.log t) ^ 2 - 1)]
  have he := Real.exp_le_exp.mpr (show 2 * Real.log t ≤ sourceUpperLogRadius t by
    unfold sourceUpperLogRadius
    nlinarith)
  rw [show 2 * Real.log t = Real.log t + Real.log t by ring,
    Real.exp_add, Real.exp_log ht] at he
  simpa only [pow_two, sourceUpperRadius] using he

/-- Any fixed multiple of the level is eventually smaller than every fine traversal radius. -/
theorem source_upper_mesh_fine_radius_growth (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t →
      A * ((j : ℝ) + 1) ≤ sourceUpperTraversalRadius t (j + 1) := by
  filter_upwards [source_upper_coarse_range_eventually,
    eventually_ge_atTop (max A (Real.exp 1))] with t ht hlarge
  have ht0 : 0 < t := (Real.exp_pos 1).trans_le ((le_max_right _ _).trans hlarge)
  have hlog : 1 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hlarge)
    simpa only [Real.log_exp] using h
  have hquad := source_upper_radius_ge_sq t ht0 hlog
  have hm : 0 < sourceUpperRadius t := Real.exp_pos _
  have hell : 1 ≤ sourceRootDepth (Real.exp t) (sourceUpperRadius t) := by
    unfold sourceRootDepth
    rw [source_upper_root_log]
    exact (Nat.one_le_floor_iff _).mpr ht
  intro j hj
  have hjell : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceUpperRadius t) := by
    unfold sourceUpperCoarseDepth at hj
    omega
  have hr := sourceRecordRadius_ge_terminal (sourceUpperRadius t) hm.le
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (j + 1) hjell
  change sourceUpperRadius t ≤ sourceUpperTraversalRadius t (j + 1) at hr
  have hjt : (j : ℝ) + 1 ≤ t := by
    have hj' : (j : ℝ) ≤ sourceUpperCoarseDepth t := by exact_mod_cast hj
    have hc := (source_upper_coarse_depth_error t ht).2
    have hD : 0 ≤ sourceUpperLogRadius t := by unfold sourceUpperLogRadius; positivity
    have hl : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hAt : A ≤ t := (le_max_left _ _).trans hlarge
  have hprod := mul_le_mul_of_nonneg_left hjt hA
  nlinarith

/-- The exact mesh buffer has the inverse-level relative size required by the sharp return gap. -/
theorem source_upper_mesh_relative_buffer (t : ℝ) (j : ℕ)
    (hr : 1000 * ((j : ℝ) + 1) ≤ sourceUpperTraversalRadius t (j + 1)) :
    sourceUpperMeshBuffer t j ≤ sourceUpperTraversalRadius t (j + 1) /
      (200 * ((j : ℝ) + 1)) := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hd : 0 < 1000 * ((j : ℝ) + 1) := by positivity
  have hf : (sourceUpperMeshSpacing t j : ℝ) ≤
      sourceUpperTraversalRadius t (j + 1) / (1000 * ((j : ℝ) + 1)) :=
    Nat.floor_le (div_nonneg (by linarith) hd.le)
  have hfm := (le_div_iff₀ hd).mp hf
  apply (le_div_iff₀ (by positivity : 0 < 200 * ((j : ℝ) + 1))).mpr
  unfold sourceUpperMeshBuffer
  nlinarith

end SRWTightness
