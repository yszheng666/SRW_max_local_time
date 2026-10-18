import SRWTightness.Exit
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MeasureTheory Filter

namespace SRWTightness

noncomputable def timeCenter (n : ℕ) : ℝ :=
  (Real.log n - Real.log (Real.log n)) / Real.sqrt Real.pi

noncomputable def diskCenter (R : ℝ) : ℝ :=
  (2 * Real.log R - Real.log (Real.log R)) / Real.sqrt Real.pi

noncomputable def timeFluctuation (n : ℕ) (ω : Sample) : ℝ :=
  Real.sqrt (maxLocalTime ω n) - timeCenter n

noncomputable def diskFluctuation (R : ℝ) (ω : Sample) : ℝ :=
  Real.sqrt (diskMax R ω) - diskCenter R

/-- Exact uniform formulation of the source time tightness theorem; currently unproved. -/
def TimeTightnessClaim : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 3 ≤ n →
    pathLaw.real {ω | K < |timeFluctuation n ω|} < ε

/-- Real-radius tightness, including each fixed bounded interval of radii. -/
def DiskTightnessClaim : Prop :=
  ∀ R₀ : ℝ, 1 < R₀ → ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
    ∀ R : ℝ, R₀ ≤ R → pathLaw.real {ω | K < |diskFluctuation R ω|} < ε

/-- Source equations (1.6) and (1.7), with constants fixed before the height. -/
def DiskTailClaim : Prop :=
  ∃ C c s₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < s₀ ∧ ∀ s : ℝ, s₀ ≤ s →
    Filter.limsup (fun R : ℝ ↦ pathLaw.real {ω | s < diskFluctuation R ω}) atTop ≤
      C * (1 + s) * Real.exp (-3 * s / 2) ∧
    Filter.limsup (fun R : ℝ ↦ pathLaw.real {ω | diskFluctuation R ω < -s}) atTop ≤
      Real.exp (-c * Real.exp (Real.sqrt Real.pi * s / 4))

/-- The exceptional infinity convention in diskMax must be discharged for each radius. -/
def ExitFiniteClaim : Prop :=
  ∀ R : ℝ, 1 < R → ∀ᵐ ω ∂pathLaw, exitTime R ω ≠ ⊤

/-- Source equation (11.9), after substituting mathfrak c = 2/sqrt(pi). -/
def TimeTailClaim : Prop :=
  ∃ C c s₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < s₀ ∧ ∀ s : ℝ, s₀ ≤ s →
    Filter.limsup (fun n : ℕ ↦ pathLaw.real {ω | s < |timeFluctuation n ω|}) atTop ≤
      2 * Real.exp (-s * Real.sqrt Real.pi / 4) +
      C * (1 + s) * Real.exp (-3 * s / 4) +
      Real.exp (-c * Real.exp (Real.sqrt Real.pi * s / 8))

/-- Same centering and all n≥3 for the inclusive endpoint convention. -/
def InclusiveTimeTightnessClaim : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 3 ≤ n →
    pathLaw.real {ω | K < |Real.sqrt (inclusiveMaxLocalTime ω n) - timeCenter n|} < ε

end SRWTightness
