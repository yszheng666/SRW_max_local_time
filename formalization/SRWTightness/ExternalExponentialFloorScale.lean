import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace SRWTightness

/-- The terminal disk radius e*m-1 when m=exp(u). -/
noncomputable def upperTerminalRadius (u : ℝ) : ℝ := Real.exp (u + 1) - 1

/-- The exact integer fine scale when m=exp(u). -/
noncomputable def upperTerminalFineRadius (u : ℝ) : ℝ := ⌊Real.exp (u / 4)⌋₊

/-- Elementary rounded-exponential growth, retained as an explicit analytic input.
There are no Green functions, random variables or probability estimates in this input. -/
def ExponentialFloorScaleInput : Prop :=
  ∀ c : ℝ, 0 < c → ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
    2 ≤ upperTerminalRadius u ∧ 1 ≤ upperTerminalFineRadius u ∧
    1 ≤ c * upperTerminalFineRadius u ∧
    64 * (c * upperTerminalFineRadius u) ≤ upperTerminalRadius u ∧
    |Real.log (upperTerminalRadius u) - u| ≤ 2 ∧
    |Real.log (upperTerminalFineRadius u) - u / 4| ≤ 1

end SRWTightness
