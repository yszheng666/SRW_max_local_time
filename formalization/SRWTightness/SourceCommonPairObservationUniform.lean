import SRWTightness.SourceCommonPairDistanceChernoff
import SRWTightness.LatticeNorm

open Filter
namespace SRWTightness

/-- The actual distance index supplies all observation-ball geometry uniformly. -/
theorem source_common_pair_observation_uniform :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      1 ≤ 2 * Real.sqrt (normSq (w - b)) ∧
      2 * (2 * Real.sqrt (normSq (w - b))) ≤ sourceCommonPairInnerRadius t j ∧
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤
        Real.log (sourceCommonPairInnerRadius t j) -
          Real.log (2 * Real.sqrt (normSq (w - b))) := by
  let L := diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 + Real.log 2 + 1
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max L (Real.log 4 + 1)))]
    with t ht hlogt
  intro b w j hbw hj
  let ρ := Real.sqrt (normSq (w - b))
  have hρ : 1 ≤ ρ := by
    have hn := one_le_normSq_of_ne_zero (w - b) (sub_ne_zero.mpr hbw.symm)
    have hs := Real.sq_sqrt (normSq_nonneg (w - b))
    have hp := Real.sqrt_nonneg (normSq (w - b))
    dsimp [ρ]
    nlinarith
  have hρ0 : 0 < ρ := by linarith
  let r := sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0
  have hr : 0 < r := by
    dsimp [r, sourceRecordRadius]
    exact mul_pos (sourceLowerRadius_pos t) (Real.exp_pos _)
  have hindex : 1 ≤ sourceCommonPairDistanceIndex t ρ := by
    have hgap : 5 ≤ sourceCommonPairGap t := by unfold sourceCommonPairGap; omega
    change j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ at hj
    omega
  have hlog : 1 ≤ Real.log (r / ρ) := (Nat.one_le_floor_iff _).mp hindex
  have he := Real.exp_le_exp.mpr (show 0 ≤ Real.log (r / ρ) by linarith)
  rw [Real.exp_zero, Real.exp_log (div_pos hr hρ0)] at he
  have houter : ρ ≤ r := (one_le_div hρ0).mp he
  have hgap := (sourceCommonPairGap_bounds t ht).1
  have hlog0 := Real.log_nonneg ht
  have hL := (le_max_left L (Real.log 4 + 1)).trans hlogt
  have h4 := (le_max_right L (Real.log 4 + 1)).trans hlogt
  have hsep := source_common_pair_observation_separation t ρ hρ0 houter j
    (sourceCommonPairGap t) hj (by linarith) (by change L ≤ _; linarith)
  exact ⟨by linarith, hsep⟩

end SRWTightness
