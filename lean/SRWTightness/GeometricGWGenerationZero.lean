import SRWTightness.GeometricMarkedListBind
import Mathlib.Tactic

open MeasureTheory

namespace SRWTightness

/-- A zero-parent generation has no positive population atom. -/
theorem geometric_gw_generation_zero_positive_atom (m : ℕ) (hm : 1 ≤ m) :
    (geometricGWGenerationLaw 0).real {m} = 0 := by
  rw [geometric_gw_generation_zero]
  have hne : m ≠ 0 := by omega
  simp [measureReal_def, Ne.symm hne]

end SRWTightness
