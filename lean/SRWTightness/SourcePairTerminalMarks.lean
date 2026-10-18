import SRWTightness.SourceActualTerminalCoordinate
import SRWTightness.SourcePairCommonThreshold

open Filter
open scoped Topology

namespace SRWTightness

/-- Both successful sites exceed the threshold in one common terminal sample vector. -/
theorem source_pair_terminal_marks :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (b w : Site) (I J : ℕ),
      1 ≤ A * diskEnergyGapRatio ^ I →
      A * diskEnergyGapRatio ^ I ≤ sourceLowerRadius t / t ^ 6 →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ (ω : Sample), domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤ →
      ∀ r : FiniteExcursionRecord
        (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1),
      sourceActualForest t b _ ω = [r] →
      ∀ (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
        (z' : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ J))),
      (y : Site) = w → (z' : Site) = w →
      ∀ β β' : ℕ → GaussianCoefficientSpace,
      (ω, β) ∈ sourceLocalTimeSuccessEvent t A γ b I z →
      (ω, β') ∈ sourceLocalTimeSuccessEvent t A γ w J z' →
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
      let k := sourceActualCount t b n ω
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let u := Real.sqrt (2 * (k : ℝ))
      let samples := terminalListSamples 0 k (finiteRecordLeaves n r)
      sourceTerminalThreshold t u ≤ normalizedMarkSum _ k α (2 / Real.pi) u z samples ∧
      sourceTerminalThreshold t u ≤ normalizedMarkSum _ k α (2 / Real.pi) u y samples := by
  filter_upwards [source_actual_terminal_coordinate,
    eventually_ge_atTop (sourceScaleThreshold 4)] with t ho ht
  intro A γ b w I J ha hcut hblo hbhi ω hfin r hr z y z' hy hz' β β' hb hw
  have hzobs := ho A b I ha hcut hblo hbhi ω hfin r hr z
  have hyobs := ho A b I ha hcut hblo hbhi ω hfin r hr y
  have hh := source_pair_common_threshold t A γ b w I J z z' hz' ht ω β β' hb hw
  dsimp only at hzobs hyobs hh ⊢
  rw [hzobs, hyobs]
  simpa only [hy] using hh

end SRWTightness
