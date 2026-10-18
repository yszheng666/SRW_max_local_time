import SRWTightness.SourceCommonSignedLevel
import SRWTightness.LatticeNorm

namespace SRWTightness

/-- A nonnegative literal common level supplies the complete pair-distance geometry. -/
theorem source_common_signed_pair_geometry (t : ℝ) (b w : Site) (j : ℕ)
    (ht : 1 ≤ t) (hbw : b ≠ w)
    (hj : (j : ℤ) = sourceSignedCommonPairLevel t (Real.sqrt (normSq (w - b)))) :
    1 ≤ Real.sqrt (normSq (w - b)) ∧
      Real.sqrt (normSq (w - b)) ≤ sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 ∧
      j + sourceCommonPairGap t =
        sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) := by
  let ρ := Real.sqrt (normSq (w - b))
  have hρ : 1 ≤ ρ := by
    have hn := one_le_normSq_of_ne_zero (w - b) (sub_ne_zero.mpr hbw.symm)
    have hs := Real.sq_sqrt (normSq_nonneg (w - b))
    have hp := Real.sqrt_nonneg (normSq (w - b))
    dsimp [ρ]
    nlinarith
  have hρ0 : 0 < ρ := by linarith
  have hi := source_common_signed_level_index_sum t ρ ht j hj
  let r := sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0
  have hr : 0 < r := by
    dsimp [r, sourceRecordRadius]
    exact mul_pos (sourceLowerRadius_pos t) (Real.exp_pos _)
  have hindex : 1 ≤ sourceCommonPairDistanceIndex t ρ := by
    have hg : 5 ≤ sourceCommonPairGap t := by unfold sourceCommonPairGap; omega
    omega
  have hlog : 1 ≤ Real.log (r / ρ) := (Nat.one_le_floor_iff _).mp hindex
  have he := Real.exp_le_exp.mpr (show 0 ≤ Real.log (r / ρ) by linarith)
  rw [Real.exp_zero, Real.exp_log (div_pos hr hρ0)] at he
  exact ⟨hρ, (one_le_div hρ0).mp he, hi⟩

end SRWTightness
