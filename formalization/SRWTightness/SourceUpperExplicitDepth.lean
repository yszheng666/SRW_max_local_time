import SRWTightness.DiskGreenExplicitAsymptotic
import SRWTightness.SourceUpperFineExpansion
import SRWTightness.SourceUpperFineDepthRatio

open Filter
open scoped Topology
namespace SRWTightness

/-- The actual upper Green depth has the explicit manuscript constant in its fine expansion. -/
theorem source_upper_depth_explicit_expansion (hinput : PotentialKernelAsymptoticInput) :
    Tendsto (fun t : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius t) -
      (sourceUpperLogRadius t + 1 + sourcePotentialConstant / (2 / Real.pi))) atTop (𝓝 0) := by
  obtain ⟨B, R₁, hB, hR₁, hb, hlim⟩ := diskGreen_explicit_asymptotic hinput
  have hg := (hlim.comp source_upper_reference_radius_tendsto).div_const (2 / Real.pi)
  have hl := log_exponential_radius_error.comp sourceUpperLogRadius_tendsto
  have hh := hg.add hl
  convert hh using 1
  · funext t
    dsimp [upperTerminalDepth, upperTerminalRadius, Function.comp_def]
    field_simp
    <;> ring
  · simp

/-- All three assertions of source (4.2), with its explicit potential constant. -/
theorem source_upper_explicit_depth_bundle (hinput : PotentialKernelAsymptoticInput) :
    Tendsto (fun t : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius t) -
      (sourceUpperLogRadius t + 1 + sourcePotentialConstant / (2 / Real.pi))) atTop (𝓝 0) ∧
    (∀ᶠ t : ℝ in atTop, |sourceUpperTotalDepth t - t| ≤
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 32 + 4) ∧
    Tendsto (fun t : ℝ ↦ Real.log (upperTerminalFineRadius (sourceUpperLogRadius t)) /
      upperTerminalDepth (sourceUpperLogRadius t)) atTop (𝓝 (1 / 4)) :=
  ⟨source_upper_depth_explicit_expansion hinput, source_upper_total_depth_internal,
    source_upper_fine_depth_ratio_internal⟩

end SRWTightness
