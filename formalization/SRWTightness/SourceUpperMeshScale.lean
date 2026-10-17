import SRWTightness.SourceUpperMeshGeometry
import SRWTightness.SourceUpperDepthEventually
import SRWTightness.SourceExcursionDomains

open Filter

namespace SRWTightness

/-- The actual upper mesh has positive spacing and admissible radii at every coarse level. -/
theorem source_upper_mesh_scale_conditions :
    ∀ᶠ t : ℝ in atTop, 32 * sourceUpperRadius t ≤ Real.exp t ∧
      ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t →
        10 ≤ sourceUpperTraversalRadius t (j + 1) ∧
        0 < sourceUpperMeshSpacing t j ∧ (sourceUpperMeshSpacing t j : ℝ) ≤ Real.exp t / 4 := by
  filter_upwards [source_upper_coarse_range_eventually,
    eventually_ge_atTop (max 1000 (Real.exp 1))] with t ht hlarge
  have ht1000 : 1000 ≤ t := (le_max_left _ _).trans hlarge
  have ht0 : 0 < t := by linarith
  have hlog : 1 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hlarge)
    simpa only [Real.log_exp] using h
  have hm : 0 < sourceUpperRadius t := Real.exp_pos _
  have hD : 0 ≤ sourceUpperLogRadius t := by unfold sourceUpperLogRadius; positivity
  have hmquad : t ^ 2 ≤ sourceUpperRadius t := by
    have hp : Real.log t ≤ (Real.log t) ^ 4 := by
      nlinarith [sq_nonneg (Real.log t - 1), sq_nonneg ((Real.log t) ^ 2 - 1)]
    have he := Real.exp_le_exp.mpr (show 2 * Real.log t ≤ sourceUpperLogRadius t by
      unfold sourceUpperLogRadius
      nlinarith)
    rw [show 2 * Real.log t = Real.log t + Real.log t by ring,
      Real.exp_add, Real.exp_log ht0] at he
    simpa only [pow_two, sourceUpperRadius] using he
  have hratio : 1 ≤ Real.exp t / (32 * sourceUpperRadius t) := by
    rw [← Real.exp_log (div_pos (Real.exp_pos t) (by positivity :
      0 < 32 * sourceUpperRadius t))]
    apply Real.one_le_exp_iff.mpr
    rw [source_upper_root_log]
    linarith
  have hR := (one_le_div (by positivity : 0 < 32 * sourceUpperRadius t)).mp hratio
  refine ⟨hR, ?_⟩
  intro j hj
  have hell : 1 ≤ sourceRootDepth (Real.exp t) (sourceUpperRadius t) := by
    unfold sourceRootDepth
    rw [source_upper_root_log]
    exact (Nat.one_le_floor_iff _).mpr ht
  have hjell : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceUpperRadius t) := by
    unfold sourceUpperCoarseDepth at hj
    omega
  have hr := sourceRecordRadius_ge_terminal (sourceUpperRadius t) hm.le
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (j + 1) hjell
  change sourceUpperRadius t ≤ sourceUpperTraversalRadius t (j + 1) at hr
  have hjt : (j : ℝ) + 1 ≤ t := by
    have hj' : (j : ℝ) ≤ sourceUpperCoarseDepth t := by exact_mod_cast hj
    have hc := (source_upper_coarse_depth_error t ht).2
    have hl : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hden : 0 < 1000 * ((j : ℝ) + 1) := by positivity
  have hsmall : 1000 * ((j : ℝ) + 1) ≤ sourceUpperTraversalRadius t (j + 1) := by
    nlinarith
  have hpos : 1 ≤ sourceUpperMeshSpacing t j :=
    (Nat.one_le_floor_iff _).mpr ((one_le_div hden).mpr hsmall)
  have hf : (sourceUpperMeshSpacing t j : ℝ) ≤
      sourceUpperTraversalRadius t (j + 1) / (1000 * ((j : ℝ) + 1)) :=
    Nat.floor_le (div_nonneg (hm.le.trans hr) hden.le)
  have hfm := (le_div_iff₀ hden).mp hf
  have hmono := sourceRecordRadius_antitone (sourceUpperRadius t) hm.le
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (Nat.zero_le (j + 1))
  have hroot := (source_root_depth_bracket (Real.exp t) (sourceUpperRadius t) hm hR).1
  change sourceUpperTraversalRadius t (j + 1) ≤ sourceUpperTraversalRadius t 0 at hmono
  change 32 * sourceUpperTraversalRadius t 0 ≤ Real.exp t at hroot
  refine ⟨by nlinarith, by omega, ?_⟩
  have ha : 0 ≤ (sourceUpperMeshSpacing t j : ℝ) := Nat.cast_nonneg _
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg ha hj0]

end SRWTightness
