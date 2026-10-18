import SRWTightness.Path
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Squared Euclidean distance to the origin. -/
def normSq (x : Site) : ℝ := (x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2

/-- The one-step drift of squared displacement, before any stopping argument. -/
theorem sum_normSq_step (x : Site) :
    ∑ d : Direction, normSq (x + step d) = 4 * (normSq x + 1) := by
  simp [Direction, Fin.sum_univ_succ, step, normSq]
  ring

/-- The mean increment is zero, in lattice coordinates. -/
theorem sum_step : ∑ d : Direction, step d = (0, 0) := by
  decide

end SRWTightness
