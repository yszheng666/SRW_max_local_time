import SRWTightness.SourceCommonPairPowerSeparation
import SRWTightness.SourceCommonPairRadiusLower
import SRWTightness.SourceForestErrorDecay

open Filter
namespace SRWTightness

/-- Actual common-radius forests have the already vanishing source error majorant. -/
theorem source_common_pair_forest_error {M : Type*}
    (B W D t ρ : ℝ) (j : ℕ) (hB : 0 ≤ B) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (ht : Real.exp 1 ≤ t) (hρ : 1 ≤ ρ)
    (houter : ρ ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (hindex : j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ)
    (hdepth : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t))
    (n : ℕ) (rs : List (FiniteExcursionRecord M n))
    (hcounts : ∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ D * t ^ 2) :
    (rs.map (finiteRecordError
      (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceCommonPairInnerRadius t j) i))
      (fun _ ↦ 2 * (W * (2 * ρ + 1) / sourceCommonPairInnerRadius t j *
        Real.log (sourceCommonPairInnerRadius t j / (2 * ρ)))) n)).sum ≤
      sourceForestQuadraticError B W D t := by
  have hcut := source_common_pair_power_separation t ρ j
    (by linarith [Real.exp_one_gt_two]) (by linarith) houter hindex
  have hh := source_forest_quadratic_count_error B W D
    (sourceCommonPairInnerRadius t j) (2 * ρ) t hB hW hD
    (sourceCommonPairInnerRadius_pos t j) (by linarith) ht hcut n rs hcounts
  apply hh.trans
  unfold sourceForestQuadraticError
  exact add_le_add
    (div_le_div_of_nonneg_left (by positivity) (sourceLowerRadius_pos t)
      (sourceCommonPairInnerRadius_ge_lower t j hdepth)) le_rfl

/-- The common-record logarithmic error is uniformly small under the barrier's population cap. -/
theorem source_common_pair_forest_error_small {M : Type*}
    (B W D : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ρ : ℝ) (j : ℕ), 1 ≤ ρ →
      ρ ≤ sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (n : ℕ) (rs : List (FiniteExcursionRecord M n)),
      (∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ D * t ^ 2) →
      (rs.map (finiteRecordError
        (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceCommonPairInnerRadius t j) i))
        (fun _ ↦ 2 * (W * (2 * ρ + 1) / sourceCommonPairInnerRadius t j *
          Real.log (sourceCommonPairInnerRadius t j / (2 * ρ)))) n)).sum < ε := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    (source_forest_quadratic_error_tendsto_zero B W D).eventually (gt_mem_nhds hε)]
    with t ht he
  intro ρ j hρ ho hi hd n rs hc
  exact (source_common_pair_forest_error B W D t ρ j hB hW hD ht hρ ho hi hd n rs hc).trans_lt he

end SRWTightness
