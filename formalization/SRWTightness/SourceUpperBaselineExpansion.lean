import SRWTightness.SourceUpperBaselineTwoSided

open Filter
open scoped Topology
namespace SRWTightness

/-- The source quadratic expansion has a uniform two-sided error throughout the height range. -/
theorem source_upper_baseline_uniform_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      |sourceUpperTarget t s ^ 2 / (2 * sourceUpperCoarseDepth t) -
        (2 * t - 2 * upperTerminalDepth (sourceUpperLogRadius t) - 2 * Real.log t +
          2 * Real.sqrt Real.pi * s - 2 * (sourceUpperTotalDepth t - t))| ≤
      C * (upperTerminalDepth (sourceUpperLogRadius t) * Real.log t / t +
        (Real.log t) ^ 2 / t) := by
  let B : ℝ := diskGreenEnergyConstant / (2 / Real.pi) + Real.log 32 + 4
  let K : ℝ := 1 + Real.sqrt Real.pi + 2 * B
  let H : ℝ := 6 + Real.sqrt Real.pi
  let C : ℝ := K ^ 2 + 2 * H * K
  have hB : 0 < B := by
    dsimp [B]
    have hl : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
    have henergy := diskGreenEnergyConstant_pos
    positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [source_upper_total_depth_internal, source_upper_coarse_linear_depth,
    eventually_ge_atTop (max (Real.exp 1) (2 * B))] with t hb hn ht
  have htExp : Real.exp 1 ≤ t := (le_max_left _ _).trans ht
  have htB : 2 * B ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := (Real.exp_pos _).trans_le htExp
  have ht1 : 1 ≤ t := by linarith [Real.exp_one_gt_two]
  have hl1 : 1 ≤ Real.log t := by
    have hh := Real.log_le_log (Real.exp_pos 1) htExp
    simpa only [Real.log_exp] using hh
  have hT : t / 2 ≤ sourceUpperTotalDepth t := by
    have hh := (abs_le.mp hb).1
    dsimp [B] at htB
    linarith
  have hN : (sourceUpperCoarseDepth t : ℝ) ≠ 0 := by
    have hh := hn.1
    linarith
  have hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
    unfold upperTerminalDepth diskGreen
    exact div_nonneg (killedGreen_nonneg _ _ _) (by positivity)
  intro s hs hslog
  let Z := (1 + Real.sqrt Real.pi) * Real.log t + 2 * B
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hZ : Z ≤ K * Real.log t := by
    have hh := mul_le_mul_of_nonneg_left hl1 (show 0 ≤ 2 * B by positivity)
    dsimp [Z, K]
    nlinarith only [hh]
  have hsq : Z ^ 2 ≤ K ^ 2 * (Real.log t) ^ 2 := by
    have hh := mul_self_le_mul_self hZ0 hZ
    nlinarith only [hh]
  have he := source_upper_baseline_two_sided t s B ht1 hB.le (by linarith)
    hs hslog hT hb hd hN
  dsimp only at he
  change _ ≤ Z ^ 2 / t + 2 * H * upperTerminalDepth (sourceUpperLogRadius t) * Z / t at he
  have hterm : Z ^ 2 / t + 2 * H * upperTerminalDepth (sourceUpperLogRadius t) * Z / t ≤
      K ^ 2 * ((Real.log t) ^ 2 / t) +
        (2 * H * K) * (upperTerminalDepth (sourceUpperLogRadius t) * Real.log t / t) := by
    have h₁ := div_le_div_of_nonneg_right hsq ht0.le
    have h₂ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hZ (show 0 ≤ 2 * H *
        upperTerminalDepth (sourceUpperLogRadius t) by positivity)) ht0.le
    calc
      _ ≤ (K ^ 2 * (Real.log t) ^ 2) / t +
          (2 * H * upperTerminalDepth (sourceUpperLogRadius t) * (K * Real.log t)) / t :=
        add_le_add h₁ h₂
      _ = _ := by ring
  have hX : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) * Real.log t / t := by positivity
  have hY : 0 ≤ (Real.log t) ^ 2 / t := by positivity
  have h₁ := mul_le_mul_of_nonneg_right
    (show K ^ 2 ≤ C by dsimp [C]; nlinarith [mul_pos hH hK]) hY
  have h₂ := mul_le_mul_of_nonneg_right
    (show 2 * H * K ≤ C by dsimp [C]; nlinarith [sq_nonneg K]) hX
  apply (he.trans hterm).trans
  calc
    _ ≤ C * ((Real.log t) ^ 2 / t) +
        C * (upperTerminalDepth (sourceUpperLogRadius t) * Real.log t / t) :=
      add_le_add h₁ h₂
    _ = _ := by ring

/-- Source (4.30) holds uniformly at all sufficiently large original real radii. -/
theorem source_upper_baseline_original_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log (Real.log R) →
      |sourceUpperTarget (Real.log R) s ^ 2 / (2 * sourceUpperCoarseDepth (Real.log R)) -
        (2 * Real.log R - 2 * upperTerminalDepth (sourceUpperLogRadius (Real.log R)) -
          2 * Real.log (Real.log R) + 2 * Real.sqrt Real.pi * s -
            2 * (sourceUpperTotalDepth (Real.log R) - Real.log R))| ≤
      C * (upperTerminalDepth (sourceUpperLogRadius (Real.log R)) *
        Real.log (Real.log R) / Real.log R + (Real.log (Real.log R)) ^ 2 / Real.log R) := by
  obtain ⟨C, hC, hh⟩ := source_upper_baseline_uniform_expansion
  exact ⟨C, hC, Real.tendsto_log_atTop.eventually hh⟩

end SRWTightness
