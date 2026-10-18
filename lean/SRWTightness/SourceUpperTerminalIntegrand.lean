import SRWTightness.SourceUpperBlockMarkListBound
import SRWTightness.SourceUpperBarrierDefinition

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The main terminal occupation bound as a function of square-root population height. -/
noncomputable def sourceUpperTerminalMain (t s C κ u : ℝ) : ℝ :=
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let q := sourceUpperTarget t s - u
  C * r ^ 2 * Real.exp (-2 * d) / d * (1 + max q 0 / Real.sqrt d) *
    Real.exp (-2 * q - κ * (max q 0) ^ 2 / d)

/-- The uniform terminal error, including the entire small-population range. -/
noncomputable def sourceUpperTerminalRemainder (t C ρ : ℝ) : ℝ :=
  C * upperTerminalFineRadius (sourceUpperLogRadius t) ^ 2 *
    Real.exp (-ρ * t ^ 2 / upperTerminalDepth (sourceUpperLogRadius t))

/-- The main terminal integrand vanishes below the source high-population cutoff. -/
noncomputable def sourceUpperTerminalIntegrand (t s C κ : ℝ) (n : ℕ)
    (g : GeometricGWRecord) : ℝ≥0∞ :=
  if t - 1 ≤ geometricGWHeight g n then
    ENNReal.ofReal (sourceUpperTerminalMain t s C κ (geometricGWHeight g n)) else 0

end SRWTightness
