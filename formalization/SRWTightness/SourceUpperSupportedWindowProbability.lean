import SRWTightness.SourceUpperTerminalWindowSupport
import SRWTightness.SourceUpperTerminalWindowProbability

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Window probabilities retain the true deficit cutoff as well as the enlarged branching endpoint. -/
theorem source_upper_supported_window_probability (hScale : ExponentialFloorScaleInput)
    (hGW : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ J : ℕ, 0 < J → (J : ℝ) ≤ t ^ 2 →
      ∀ u : ℝ, t - 1 ≤ u →
      geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)
        {g | g ∈ sourceUpperGWBand t s (sourceUpperBlockRoot t b)
            (sourceUpperBlockForestDepth t b) ∧
          geometricGWHeight g (sourceUpperBlockForestDepth t b) ∈ Set.Ico u (u + 1)} ≤
        if -(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤
            sourceUpperTarget t s - u ∧ u ≤ sourceUpperBranchingEnd t s then
          ENNReal.ofReal (sourceUpperBranchingWindowFactor t s C (sourceUpperBlockRoot t b) J u)
        else 0 := by
  obtain ⟨C, hC, hp⟩ := source_upper_terminal_window_probability hScale hGW
  refine ⟨C, hC, ?_⟩
  filter_upwards [hp, source_upper_terminal_window_deficit hScale] with t ht he
  intro b hb s hs hslog J hJ hJcap u hu
  by_cases hq : -(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤
      sourceUpperTarget t s - u
  · simpa only [hq, true_and] using ht b hb s hs hslog J hJ hJcap u hu
  · simp only [hq, false_and, ite_false]
    have hempty :
        {g : GeometricGWRecord |
          g ∈ sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b) ∧
          geometricGWHeight g (sourceUpperBlockForestDepth t b) ∈ Set.Ico u (u + 1)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      exact hq (he b hb s g hg.1 u hg.2.1)
    rw [hempty, measure_empty]

end SRWTightness
