import SRWTightness.SourceUpperBoundedThreshold
import SRWTightness.SourceUpperHeightSlack

open Filter
open scoped Topology
namespace SRWTightness

/-- The logarithmic fourth-power scale dominates the required square-root margin. -/
theorem upper_log_height_margin (L B d : ℝ) (hB : 0 ≤ B) (hL : B + 10 ≤ L)
    (hd : (8 * L) ^ 4 - B ≤ d) :
    16 ≤ d ∧ L + 5 ≤ Real.sqrt d / 2 := by
  have hL0 : 10 ≤ L := by linarith
  have hL2 : L ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hL4 : L ^ 2 ≤ L ^ 4 := by nlinarith [sq_nonneg (L ^ 2 - 1)]
  have hdsq : (2 * (L + 5)) ^ 2 ≤ d := by nlinarith
  have hs := Real.le_sqrt_of_sq_le hdsq
  constructor <;> nlinarith

/-- The actual Green depth eventually has a full unit of terminal-height slack. -/
theorem source_upper_height_margin_eventually (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop,
      16 ≤ upperTerminalDepth (sourceUpperLogRadius t) ∧
      Real.log t + 5 ≤ Real.sqrt (upperTerminalDepth (sourceUpperLogRadius t)) / 2 := by
  let B := diskGreenEnergyConstant / (2 / Real.pi) + 2
  have hB : 0 ≤ B := by
    have hg := diskGreenEnergyConstant_pos
    dsimp [B]
    positivity
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (B + 10))
  filter_upwards [source_upper_terminal_depth_eventually hScale, hl] with t hd ht
  have hh := (abs_le.mp hd).1
  apply upper_log_height_margin (Real.log t) B _ hB ht
  change (8 * Real.log t) ^ 4 - B ≤ upperTerminalDepth (sourceUpperLogRadius t)
  change -B ≤ upperTerminalDepth (sourceUpperLogRadius t) - (8 * Real.log t) ^ 4 at hh
  linarith

/-- Every unit downward perturbation is admissible over the source terminal barrier. -/
theorem source_upper_perturbed_height_eventually (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s u ε : ℝ, s ≤ Real.log t →
      u ≤ sourceUpperTarget t s + (4 + s) +
        upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) →
      -1 ≤ ε → -Real.sqrt (upperTerminalDepth (sourceUpperLogRadius t)) ≤
        (sourceUpperTarget t s - u) + ε := by
  filter_upwards [source_upper_height_margin_eventually hScale] with t ht
  intro s u ε hs hu hε
  apply terminal_perturbed_height_admissible _ (Real.log t) _ ε ht.1 ht.2 _ hε
  linarith

/-- The actual source threshold has both a bounded error and terminal Gaussian admissibility. -/
theorem source_upper_admissible_threshold (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ u : ℝ,
      t - 1 ≤ u → u ≤ sourceUpperTarget t s + (4 + s) +
        upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) →
      ∃ ε : ℝ,
        Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ) / (2 / Real.pi)) -
          Real.sqrt (sourceUpperIntensity t / (2 / Real.pi)) * u =
          2 * upperTerminalDepth (sourceUpperLogRadius t) + (sourceUpperTarget t s - u) + ε ∧
        |ε| ≤ 1 ∧ -Real.sqrt (upperTerminalDepth (sourceUpperLogRadius t)) ≤
          (sourceUpperTarget t s - u) + ε := by
  filter_upwards [source_upper_bounded_threshold hScale 1 (by norm_num),
    source_upper_perturbed_height_eventually hScale] with t ht ha
  intro s hs hslog u hu hbar
  obtain ⟨ε, heq, he⟩ := ht s hs hslog u hu hbar
  exact ⟨ε, heq, he, ha s u ε hslog hbar (abs_le.mp he).1⟩

end SRWTightness
