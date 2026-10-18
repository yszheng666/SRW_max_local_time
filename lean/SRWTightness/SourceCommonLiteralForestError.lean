import SRWTightness.SourceCommonLiteralTerminalError
import SRWTightness.SourceCommonLiteralError
import SRWTightness.SourceForestQuadraticError

open scoped BigOperators

namespace SRWTightness

/-- The actual common forest error is bounded by the literal expression with fixed constants. -/
theorem source_common_forest_literal_error {M : Type*}
    (B W D t ρ : ℝ) (j : ℕ) (hB : 0 ≤ B) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (ht : 1 ≤ t) (hρ : 1 ≤ ρ)
    (houter : ρ ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (hindex : j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ)
    (n : ℕ) (rs : List (FiniteExcursionRecord M n))
    (hcounts : ∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ D * t ^ 2) :
    (rs.map (finiteRecordError
      (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceCommonPairInnerRadius t j) i))
      (fun _ ↦ 2 * (W * (2 * ρ + 1) / sourceCommonPairInnerRadius t j *
        Real.log (sourceCommonPairInnerRadius t j / (2 * ρ)))) n)).sum ≤
      sourceCommonLiteralError (16 * B * D + 6 * Real.exp 1 * W * D) t j := by
  let m := sourceCommonPairInnerRadius t j
  let q := ((sourceCommonPairGap t : ℝ) + 1) * Real.exp (-(sourceCommonPairGap t : ℝ))
  let C := 16 * B * D + 6 * Real.exp 1 * W * D
  have hm : 0 < m := sourceCommonPairInnerRadius_pos t j
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcut := source_common_pair_power_separation t ρ j ht (by linarith) houter hindex
  have hsep : 2 * ρ ≤ m := hcut.trans (div_le_self hm.le (one_le_pow₀ ht))
  have hlog : 0 ≤ Real.log (m / (2 * ρ)) :=
    Real.log_nonneg ((one_le_div (by positivity)).mpr hsep)
  have hb := forest_error_population_bound
    (fun i ↦ 4 * (B * 14 / growingRecordRadius m i))
    (2 * (W * (2 * ρ + 1) / m * Real.log (m / (2 * ρ)))) n rs
    (fun _ ↦ D * t ^ 2) (by intro i hi; dsimp [growingRecordRadius]; positivity)
    (by positivity) hcounts
  have hsum : (∑ i ∈ Finset.range n,
      (D * t ^ 2 + D * t ^ 2) * (4 * (B * 14 / growingRecordRadius m i))) ≤
      224 * B * D * t ^ 2 / m := by
    calc
      _ = (112 * B * D * t ^ 2) * ∑ i ∈ Finset.range n, 1 / growingRecordRadius m i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ (112 * B * D * t ^ 2) * (2 / m) :=
        mul_le_mul_of_nonneg_left (growing_record_reciprocal_sum m hm n) (by positivity)
      _ = _ := by ring
  have hterm : (2 * (W * (2 * ρ + 1) / m * Real.log (m / (2 * ρ)))) * (D * t ^ 2) ≤
      6 * Real.exp 1 * W * D * t ^ 2 * q := by
    have h := mul_le_mul_of_nonneg_left
      (source_common_terminal_literal_error t ρ j ht hρ houter hindex)
      (show 0 ≤ 2 * W * D * t ^ 2 by positivity)
    calc
      _ = (2 * W * D * t ^ 2) *
          ((2 * ρ + 1) / m * Real.log (m / (2 * ρ))) := by ring
      _ ≤ (2 * W * D * t ^ 2) * (3 * Real.exp 1 *
          ((sourceCommonPairGap t : ℝ) + 1) * Real.exp (-(sourceCommonPairGap t : ℝ))) := h
      _ = _ := by dsimp [q]; ring
  have hc1 : 16 * B * D ≤ C := le_add_of_nonneg_right (by positivity)
  have hc2 : 6 * Real.exp 1 * W * D ≤ C := le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ 224 * B * D * t ^ 2 / m + 6 * Real.exp 1 * W * D * t ^ 2 * q :=
      hb.trans (add_le_add hsum hterm)
    _ = t ^ 2 * ((16 * B * D) * (14 / m) + (6 * Real.exp 1 * W * D) * q) := by ring
    _ ≤ t ^ 2 * (C * (14 / m) + C * q) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right hc1 (by positivity))
        (mul_le_mul_of_nonneg_right hc2 hq)) (sq_nonneg t)
    _ = _ := by dsimp [C, m, q, sourceCommonLiteralError]; ring

end SRWTightness
