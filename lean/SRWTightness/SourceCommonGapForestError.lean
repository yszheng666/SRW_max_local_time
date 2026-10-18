import SRWTightness.CommonGapTerminalError
import SRWTightness.ForestPopulationError
import SRWTightness.GrowingRecordReciprocalSum

open scoped BigOperators
namespace SRWTightness

/-- The complete common-record error at an arbitrary admissible gap, using a population bound
at its own depth. Both boundary and terminal observation costs are retained. -/
theorem source_common_gap_forest_error {M : Type*}
    (B W D t ρ : ℝ) (j J n : ℕ) (hB : 0 ≤ B) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hρ : 1 ≤ ρ)
    (houter : ρ ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (hindex : j + J = sourceCommonPairDistanceIndex t ρ)
    (hsep : 2 * ρ ≤ sourceCommonPairInnerRadius t j)
    (rs : List (FiniteExcursionRecord M n))
    (hcounts : ∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ D * ((n : ℝ) + 1) ^ 2) :
    (rs.map (finiteRecordError
      (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceCommonPairInnerRadius t j) i))
      (fun _ ↦ 2 * (W * (2 * ρ + 1) / sourceCommonPairInnerRadius t j *
        Real.log (sourceCommonPairInnerRadius t j / (2 * ρ)))) n)).sum ≤
      224 * B * D * ((n : ℝ) + 1) ^ 2 / sourceCommonPairInnerRadius t j +
        6 * Real.exp 1 * W * D * ((n : ℝ) + 1) ^ 2 * ((J : ℝ) + 1) *
          Real.exp (-(J : ℝ)) := by
  let m := sourceCommonPairInnerRadius t j
  have hm : 0 < m := sourceCommonPairInnerRadius_pos t j
  have hlog : 0 ≤ Real.log (m / (2 * ρ)) :=
    Real.log_nonneg ((one_le_div (by linarith : 0 < 2 * ρ)).mpr hsep)
  have hb := forest_error_population_bound
    (fun i ↦ 4 * (B * 14 / growingRecordRadius m i))
    (2 * (W * (2 * ρ + 1) / m * Real.log (m / (2 * ρ)))) n rs
    (fun _ ↦ D * ((n : ℝ) + 1) ^ 2)
    (by intro i hi; dsimp [growingRecordRadius]; positivity) (by positivity) hcounts
  have hsum : (∑ i ∈ Finset.range n,
      (D * ((n : ℝ) + 1) ^ 2 + D * ((n : ℝ) + 1) ^ 2) *
        (4 * (B * 14 / growingRecordRadius m i))) ≤
      224 * B * D * ((n : ℝ) + 1) ^ 2 / m := by
    calc
      _ = (112 * B * D * ((n : ℝ) + 1) ^ 2) *
          ∑ i ∈ Finset.range n, 1 / growingRecordRadius m i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ (112 * B * D * ((n : ℝ) + 1) ^ 2) * (2 / m) :=
        mul_le_mul_of_nonneg_left (growing_record_reciprocal_sum m hm n) (by positivity)
      _ = _ := by ring
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (source_common_gap_terminal_error W t ρ j J hW hρ houter hindex hsep)
      (by norm_num : (0 : ℝ) ≤ 2))
    (show 0 ≤ D * ((n : ℝ) + 1) ^ 2 by positivity)
  exact hb.trans ((add_le_add hsum hterm).trans_eq (by dsimp [m]; ring))

end SRWTightness
