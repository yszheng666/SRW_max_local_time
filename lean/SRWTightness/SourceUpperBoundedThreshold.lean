import SRWTightness.SourceUpperManuscriptThreshold

open Filter
open scoped Topology
namespace SRWTightness

/-- The source threshold error is uniformly smaller than any fixed positive tolerance. -/
theorem source_upper_bounded_threshold (hScale : ExponentialFloorScaleInput)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ u : ℝ,
      t - 1 ≤ u → u ≤ sourceUpperTarget t s + (4 + s) +
        upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) →
      ∃ ε : ℝ,
        Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ) / (2 / Real.pi)) -
          Real.sqrt (sourceUpperIntensity t / (2 / Real.pi)) * u =
          2 * upperTerminalDepth (sourceUpperLogRadius t) + (sourceUpperTarget t s - u) + ε ∧
        |ε| ≤ η := by
  obtain ⟨C, _, hlim, ht⟩ := source_upper_manuscript_threshold hScale
  have hc : Tendsto (fun t ↦ C * sourceUpperThresholdErrorScale t) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul C
  filter_upwards [ht, hc.eventually (eventually_lt_nhds hη)] with t ht he
  intro s hs hslog u hu hbar
  obtain ⟨ε, hε, hb⟩ := ht s hs hslog u hu hbar
  exact ⟨ε, hε, hb.trans he.le⟩

end SRWTightness
