import SRWTightness.SourceUpperMarkParameters

namespace SRWTightness

/-- Exact baseline quadratic expansion underlying source (4.30), before asymptotic error bounds. -/
theorem source_upper_baseline_quadratic (t s : ℝ)
    (hT : sourceUpperTotalDepth t ≠ 0) (hN : (sourceUpperCoarseDepth t : ℝ) ≠ 0) :
    let T := sourceUpperTotalDepth t
    let d := upperTerminalDepth (sourceUpperLogRadius t)
    let z := sourceUpperHeight t s - 2 * T
    sourceUpperTarget t s ^ 2 / (2 * sourceUpperCoarseDepth t) =
      2 * t - 2 * d - 2 * Real.log t + 2 * Real.sqrt Real.pi * s - 2 * (T - t) +
        (z ^ 2 / (2 * T) - d * z * (sourceUpperHeight t s + 2 * T) / (2 * T ^ 2)) := by
  dsimp only
  unfold sourceUpperTarget sourceUpperSlope
  have hT' : (sourceUpperCoarseDepth t : ℝ) +
      upperTerminalDepth (sourceUpperLogRadius t) ≠ 0 := hT
  unfold sourceUpperTotalDepth sourceUpperHeight
  field_simp [hN, hT'] <;> ring

end SRWTightness
