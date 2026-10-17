import SRWTightness.SourceForestContinuationCoordinates
import SRWTightness.SourceEarlyRootCap
import SRWTightness.SourceRootCoarseCounts

open Filter
namespace SRWTightness

/-- The remaining coarse band and its initial root cap control every forest generation. -/
theorem source_remaining_forest_cap {M : Type*} (t : ℝ) (ν n : ℕ)
    (ht : 2 ≤ t) (hθ : 0 ≤ sourceBarrierSlope t)
    (hline : sourceBarrierSlope t * ((ν + n : ℕ) : ℝ) ≤ 2 * t)
    (hT : ((ν + n : ℕ) : ℝ) ≤ sourceTotalTime t)
    (rs : List (FiniteExcursionRecord M n)) (hk : rs.length ≤ sourceEarlyRootCap t ν)
    (hb : forestPopulationList n rs ∈ sourceContinuationBand t ν n) :
    ∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ 8 * t ^ 2 := by
  intro i hi
  have hν : (ν : ℝ) ≤ ((ν + n : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right ν n
  have hbase : 4 + sourceBarrierSlope t * (ν : ℝ) ≤ 4 * t := by
    linarith [mul_le_mul_of_nonneg_left hν hθ]
  by_cases hj0 : n - i = 0
  · have he : i = n := by omega
    subst i
    have hr : forestLevelPopulation n rs n = rs.length := by
      simp [forestLevelPopulation, finiteRecordLevelPopulation_root]
    rw [hr]
    have hkR : (rs.length : ℝ) ≤ (sourceEarlyRootCap t ν : ℝ) := Nat.cast_le.mpr hk
    have hf := Nat.floor_le
      (show 0 ≤ (4 + sourceBarrierSlope t * (ν : ℝ)) ^ 2 / 2 by positivity)
    change (sourceEarlyRootCap t ν : ℝ) ≤ _ at hf
    have hn : 0 ≤ 4 + sourceBarrierSlope t * (ν : ℝ) := by positivity
    nlinarith
  · have hj : n - i ≤ n := by omega
    have hidx : ((ν + (n - i) : ℕ) : ℝ) ≤ ((ν + n : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_left hj ν
    have hcurv := Real.rpow_nonneg
      (le_min (Nat.cast_nonneg (ν + (n - i))) (sub_nonneg.mpr (hidx.trans hT))) (2 / 5 : ℝ)
    have hh := hb.1 (n - i) (by omega) hj
    unfold sourceCommonPairEndpoint at hh
    have hheight : geometricGWHeight (forestPopulationList n rs) (n - i) ≤ 4 * t := by
      linarith [mul_le_mul_of_nonneg_left hidx hθ]
    rw [geometricGWHeight, forest_gw_population n rs (n - i) hj,
      Nat.sub_sub_self hi] at hheight
    have hs := Real.sq_sqrt (show 0 ≤ 2 * (forestLevelPopulation n rs i : ℝ) by positivity)
    have hn := Real.sqrt_nonneg (2 * (forestLevelPopulation n rs i : ℝ))
    nlinarith

/-- The actual remaining depth satisfies the forest cap uniformly at every valid split level. -/
theorem source_remaining_forest_population_cap :
    ∀ᶠ t : ℝ in atTop, ∀ ν : ℕ,
      ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)
      ∀ (M : Type*) (rs : List (FiniteExcursionRecord M n)),
      rs.length ≤ sourceEarlyRootCap t ν →
      forestPopulationList n rs ∈ sourceContinuationBand t ν n →
      ∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ 8 * t ^ 2 := by
  filter_upwards [source_deficit_large_conditions, source_root_gw_horizon_large] with t ht hn
  intro ν hν
  dsimp only
  intro M rs hk hb
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  have hβ := sourceBarrierSlope_bounds t ht.1 ht.2.1
  have hd := sourceLowerTime_ge_one t ht.1
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hgap := sourceTerminalRoot_gap t 0 ht.1 ht.2.1
  have hθN : sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) ≤ 2 * t := by
    dsimp [sourceTerminalRoot, sourceTerminalHeight] at hgap
    nlinarith [mul_nonneg hβ.1 (show 0 ≤ sourceLowerTime (sourceLowerRadius t) by linarith)]
  have he : ν + (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) =
      sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by omega
  apply source_remaining_forest_cap t ν _ ht2 hβ.1 _ _ rs hk hb
  · rw [he, hn.2]
    exact hθN
  · rw [he, hn.2]
    unfold sourceTotalTime
    linarith

end SRWTightness
