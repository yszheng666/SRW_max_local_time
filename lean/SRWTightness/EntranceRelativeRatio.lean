import SRWTightness.SourceEntranceAllRadii

namespace SRWTightness

/-- A positive actual atom and a relative mass bound imply the conventional ratio formulation. -/
theorem positive_atom_ratio_of_relative_error (p r ε : ℝ) (hp : 0 < p) (hr : 0 ≤ r)
    (hb : |p - r| ≤ ε * r) : 0 < r ∧ |p / r - 1| ≤ ε := by
  have hr0 : 0 < r := by
    by_contra h
    have he : r = 0 := le_antisymm (le_of_not_gt h) hr
    rw [he, mul_zero, sub_zero, abs_of_pos hp] at hb
    linarith
  refine ⟨hr0, ?_⟩
  rw [show p / r - 1 = (p - r) / r by field_simp, abs_div, abs_of_pos hr0]
  exact (div_le_iff₀ hr0).mpr hb

end SRWTightness
