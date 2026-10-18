import SRWTightness.SourceUpperBaselineNormalization
import SRWTightness.SourceUpperActualRootDepthCost

open Filter

namespace SRWTightness

/-- The actual remaining-depth normalization combines baseline tail decay and root damping. -/
theorem source_upper_reduced_baseline (hScale : ExponentialFloorScaleInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      let k := sourceUpperBlockRoot t b
      let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
      Real.exp (2 * t - 2 * upperTerminalDepth (sourceUpperLogRadius t) -
        sourceUpperTarget t s ^ 2 / (2 * L)) / L ^ 2 ≤
        C * Real.exp (-(2 * Real.sqrt Real.pi * s)) * Real.exp (-(9 * (k : ℝ) / 8)) := by
  obtain ⟨C, hC, hb⟩ := source_upper_baseline_exponential hScale
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [hb, source_upper_actual_root_depth_exponential hScale,
    source_upper_branching_depth_bounds, source_upper_coarse_linear_depth,
    eventually_ge_atTop (1 : ℝ)] with t ht hr hd hN ht1
  intro b hb s hs hslog
  dsimp only
  let k := sourceUpperBlockRoot t b
  let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
  let N : ℝ := sourceUpperCoarseDepth t
  let x := sourceUpperTarget t s
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  have hL : 0 < L := by dsimp [L, k]; linarith [(hd b hb).2.1]
  have hN0 : 0 < N := by dsimp [N]; linarith [hN.1]
  have hratio : N ^ 2 / L ^ 2 ≤ 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    have hLl : t / 2 ≤ L := by dsimp [L, k]; linarith [(hd b hb).2.1]
    have hNu : N ≤ t := hN.2
    nlinarith
  have hbase : Real.exp (2 * t - 2 * d - x ^ 2 / (2 * N)) / N ^ 2 ≤
      C * Real.exp (-(2 * Real.sqrt Real.pi * s)) := ht s hs hslog
  have hroot : Real.exp (-x ^ 2 / (2 * L)) ≤
      Real.exp (-x ^ 2 / (2 * N)) * Real.exp (-(9 * (k : ℝ) / 8)) := by
    simpa only [neg_div] using hr b hb s hs hslog
  have hnormal : Real.exp (2 * t - 2 * d) * Real.exp (-x ^ 2 / (2 * N)) =
      Real.exp (2 * t - 2 * d - x ^ 2 / (2 * N)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (2 * t - 2 * d) * Real.exp (-x ^ 2 / (2 * L))) / L ^ 2 := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ (Real.exp (2 * t - 2 * d) *
        (Real.exp (-x ^ 2 / (2 * N)) * Real.exp (-(9 * (k : ℝ) / 8)))) / L ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hroot (Real.exp_nonneg _)) (sq_nonneg _)
    _ = (N ^ 2 / L ^ 2) *
        (Real.exp (2 * t - 2 * d - x ^ 2 / (2 * N)) / N ^ 2) *
          Real.exp (-(9 * (k : ℝ) / 8)) := by
      rw [← mul_assoc, hnormal]
      field_simp
    _ ≤ 4 * (C * Real.exp (-(2 * Real.sqrt Real.pi * s))) *
        Real.exp (-(9 * (k : ℝ) / 8)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul hratio hbase (by positivity) (by norm_num)
    _ = _ := by ring

end SRWTightness
