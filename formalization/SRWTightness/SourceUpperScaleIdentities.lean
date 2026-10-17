import SRWTightness.ExternalExponentialFloorScale
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SRWTightness

/-- The terminal radius agrees exactly with e*m-1 for m=exp(u). -/
theorem upperTerminalRadius_source_identity (u : ℝ) :
    upperTerminalRadius u = Real.exp 1 * Real.exp u - 1 := by
  simp [upperTerminalRadius, Real.exp_add, mul_comm]

/-- The fine scale agrees exactly with floor(m^(1/4)) for m=exp(u). -/
theorem upperTerminalFineRadius_source_identity (u : ℝ) :
    upperTerminalFineRadius u = (⌊(Real.exp u) ^ (1 / 4 : ℝ)⌋₊ : ℝ) := by
  have he : Real.exp (u / 4) = (Real.exp u) ^ (1 / 4 : ℝ) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  simp only [upperTerminalFineRadius, he]

end SRWTightness
