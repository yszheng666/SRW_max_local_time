import SRWTightness.IntegerUnitChain
import SRWTightness.Geometry

namespace SRWTightness

/-- A horizontal nearest-neighbor segment with a fixed second coordinate. -/
def horizontalUnitChain (a b c : ℤ) (n : ℕ) : Site := (integerUnitChain a b n, c)

/-- Horizontal chains have their literal lattice endpoints. -/
theorem horizontalUnitChain_endpoints (a b c : ℤ) :
    horizontalUnitChain a b c 0 = (a, c) ∧
      horizontalUnitChain a b c (b - a).natAbs = (b, c) := by
  simp [horizontalUnitChain, integerUnitChain_zero, integerUnitChain_end]

/-- Each horizontal chain step has squared Euclidean length at most one. -/
theorem horizontalUnitChain_step (a b c : ℤ) (n : ℕ) :
    normSq (horizontalUnitChain a b c (n + 1) - horizontalUnitChain a b c n) ≤ 1 := by
  have hi := integerUnitChain_step a b n
  have hr : |((integerUnitChain a b (n + 1) - integerUnitChain a b n : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast hi
  have hs := (sq_le_one_iff_abs_le_one _).mpr hr
  simp only [normSq, horizontalUnitChain, Prod.fst_sub, Prod.snd_sub, sub_self,
    Int.cast_sub, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at *
  exact hs

/-- Horizontal segments stay within the coordinate box of their endpoints. -/
theorem horizontalUnitChain_box (a b c : ℤ) (M : ℝ)
    (ha : |(a : ℝ)| ≤ M) (hb : |(b : ℝ)| ≤ M) (hc : |(c : ℝ)| ≤ M) (n : ℕ) :
    normSq (horizontalUnitChain a b c n) ≤ 2 * M ^ 2 := by
  have hi := integerUnitChain_between a b n
  have hlo : min (a : ℝ) (b : ℝ) ≤ (integerUnitChain a b n : ℝ) := by
    exact_mod_cast hi.1
  have hhi : (integerUnitChain a b n : ℝ) ≤ max (a : ℝ) (b : ℝ) := by
    exact_mod_cast hi.2
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have hleft : -M ≤ (integerUnitChain a b n : ℝ) :=
    (le_min ha'.1 hb'.1).trans hlo
  have hright : (integerUnitChain a b n : ℝ) ≤ M :=
    hhi.trans (max_le ha'.2 hb'.2)
  dsimp [normSq, horizontalUnitChain]
  nlinarith [sq_nonneg (M - (integerUnitChain a b n : ℝ)),
    mul_nonneg (sub_nonneg.mpr hright) (by linarith : 0 ≤ M + (integerUnitChain a b n : ℝ)),
    mul_nonneg (sub_nonneg.mpr hc'.2) (by linarith : 0 ≤ M + (c : ℝ))]

/-- The fixed coordinate gives a lower radial bound along the whole horizontal segment. -/
theorem horizontalUnitChain_fixed_lower (a b c : ℤ) (n : ℕ) :
    (c : ℝ) ^ 2 ≤ normSq (horizontalUnitChain a b c n) := by
  dsimp [normSq, horizontalUnitChain]
  nlinarith [sq_nonneg (integerUnitChain a b n : ℝ)]

/-- Extending a coordinate away from zero cannot decrease the starting radius. -/
theorem horizontalUnitChain_outward (a b c : ℤ)
    (hab : (0 ≤ a ∧ a ≤ b) ∨ (b ≤ a ∧ a ≤ 0)) (n : ℕ) :
    normSq (a, c) ≤ normSq (horizontalUnitChain a b c n) := by
  have hi := integerUnitChain_between a b n
  rcases hab with h | h
  · have hh : a ≤ integerUnitChain a b n := by omega
    have hh' : (a : ℝ) ≤ (integerUnitChain a b n : ℝ) := by exact_mod_cast hh
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast h.1
    dsimp [normSq, horizontalUnitChain]
    nlinarith [sq_nonneg ((integerUnitChain a b n : ℝ) - a)]
  · have hh : integerUnitChain a b n ≤ a := by omega
    have hh' : (integerUnitChain a b n : ℝ) ≤ (a : ℝ) := by exact_mod_cast hh
    have ha : (a : ℝ) ≤ 0 := by exact_mod_cast h.2
    dsimp [normSq, horizontalUnitChain]
    nlinarith [sq_nonneg ((integerUnitChain a b n : ℝ) - a)]

end SRWTightness
