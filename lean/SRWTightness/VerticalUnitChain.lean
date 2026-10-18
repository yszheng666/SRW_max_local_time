import SRWTightness.AxisUnitChain

namespace SRWTightness

/-- A vertical nearest-neighbor segment with a fixed first coordinate. -/
def verticalUnitChain (a b c : ℤ) (n : ℕ) : Site := (c, integerUnitChain a b n)

/-- Swapping the coordinates preserves the radial profile of an axis segment. -/
theorem verticalUnitChain_normSq (a b c : ℤ) (n : ℕ) :
    normSq (verticalUnitChain a b c n) = normSq (horizontalUnitChain a b c n) := by
  simp only [normSq, verticalUnitChain, horizontalUnitChain, add_comm]

/-- Vertical chains have their literal lattice endpoints. -/
theorem verticalUnitChain_endpoints (a b c : ℤ) :
    verticalUnitChain a b c 0 = (c, a) ∧
      verticalUnitChain a b c (b - a).natAbs = (c, b) := by
  simp [verticalUnitChain, integerUnitChain_zero, integerUnitChain_end]

/-- Each vertical chain step has squared Euclidean length at most one. -/
theorem verticalUnitChain_step (a b c : ℤ) (n : ℕ) :
    normSq (verticalUnitChain a b c (n + 1) - verticalUnitChain a b c n) ≤ 1 := by
  have h := horizontalUnitChain_step a b c n
  simpa only [normSq, horizontalUnitChain, verticalUnitChain,
    Prod.fst_sub, Prod.snd_sub, add_comm] using h

/-- Vertical segments stay within the coordinate box of their endpoints. -/
theorem verticalUnitChain_box (a b c : ℤ) (M : ℝ)
    (ha : |(a : ℝ)| ≤ M) (hb : |(b : ℝ)| ≤ M) (hc : |(c : ℝ)| ≤ M) (n : ℕ) :
    normSq (verticalUnitChain a b c n) ≤ 2 * M ^ 2 := by
  rw [verticalUnitChain_normSq]
  exact horizontalUnitChain_box a b c M ha hb hc n

/-- The fixed coordinate gives a lower radial bound along the whole vertical segment. -/
theorem verticalUnitChain_fixed_lower (a b c : ℤ) (n : ℕ) :
    (c : ℝ) ^ 2 ≤ normSq (verticalUnitChain a b c n) := by
  rw [verticalUnitChain_normSq]
  exact horizontalUnitChain_fixed_lower a b c n

end SRWTightness
