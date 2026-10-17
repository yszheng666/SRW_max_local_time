import SRWTightness.VerticalUnitChain

namespace SRWTightness

/-- Place the moving coordinate horizontally or vertically. -/
def axisSite (vertical : Bool) (a c : ℤ) : Site :=
  if vertical then (c, a) else (a, c)

/-- An integer segment in either coordinate direction. -/
def axisUnitChain (vertical : Bool) (a b c : ℤ) (n : ℕ) : Site :=
  axisSite vertical (integerUnitChain a b n) c

/-- Axis chains start and end at the specified coordinate placements. -/
theorem axisUnitChain_endpoints (t : Bool) (a b c : ℤ) :
    axisUnitChain t a b c 0 = axisSite t a c ∧
      axisUnitChain t a b c (b - a).natAbs = axisSite t b c := by
  simp [axisUnitChain, integerUnitChain_zero, integerUnitChain_end]

/-- The two orientations have the same radial profile. -/
theorem axisUnitChain_normSq (t : Bool) (a b c : ℤ) (n : ℕ) :
    normSq (axisUnitChain t a b c n) = normSq (horizontalUnitChain a b c n) := by
  cases t <;> simp [axisUnitChain, axisSite, horizontalUnitChain, normSq, add_comm]

/-- Consecutive axis points have squared Euclidean distance at most one. -/
theorem axisUnitChain_step (t : Bool) (a b c : ℤ) (n : ℕ) :
    normSq (axisUnitChain t a b c (n + 1) - axisUnitChain t a b c n) ≤ 1 := by
  cases t
  · exact horizontalUnitChain_step a b c n
  · exact verticalUnitChain_step a b c n

/-- The length of an axis segment is bounded by its coordinate enclosure. -/
theorem axisUnitChain_length_bound (a b : ℤ) (M : ℝ)
    (ha : |(a : ℝ)| ≤ M) (hb : |(b : ℝ)| ≤ M) : ((b - a).natAbs : ℝ) ≤ 2 * M := by
  have he : ((b - a).natAbs : ℝ) = |(b : ℝ) - a| := by
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
  rw [he]
  have ht := abs_sub (b : ℝ) (a : ℝ)
  linarith

end SRWTightness
