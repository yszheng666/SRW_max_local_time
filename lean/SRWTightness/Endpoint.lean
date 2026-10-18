import SRWTightness.Targets
import Mathlib.Tactic.Linarith

open MeasureTheory

namespace SRWTightness

/-- The endpoint convention changes the square-root maximum by at most one. -/
theorem sqrt_inclusive_bounds (ω : Sample) (n : ℕ) :
    Real.sqrt (maxLocalTime ω n) ≤ Real.sqrt (inclusiveMaxLocalTime ω n) ∧
    Real.sqrt (inclusiveMaxLocalTime ω n) ≤ Real.sqrt (maxLocalTime ω n) + 1 := by
  rw [inclusiveMaxLocalTime_eq]
  constructor
  · exact Real.sqrt_le_sqrt (Nat.cast_le.mpr (maxLocalTime_mono ω (Nat.le_succ n)))
  · apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have h : (maxLocalTime ω (n + 1) : ℝ) ≤ (maxLocalTime ω n + 1 : ℕ) :=
        Nat.cast_le.mpr (maxLocalTime_succ_le ω n)
      have hs := Real.sq_sqrt (Nat.cast_nonneg (maxLocalTime ω n))
      have hn := Real.sqrt_nonneg (maxLocalTime ω n : ℝ)
      push_cast at h
      nlinarith

/-- A logical transfer only: the premise is the still-unproved main time theorem. -/
theorem inclusive_tightness_of_time (ht : TimeTightnessClaim) : InclusiveTimeTightnessClaim := by
  intro ε hε
  obtain ⟨K, hK, hb⟩ := ht ε hε
  refine ⟨K + 1, by linarith, ?_⟩
  intro n hn
  apply lt_of_le_of_lt (measureReal_mono (s₁ :=
    {ω | K + 1 < |Real.sqrt (inclusiveMaxLocalTime ω n) - timeCenter n|})
    (s₂ := {ω | K < |timeFluctuation n ω|}) ?_) (hb n hn)
  intro ω hω
  change K < |Real.sqrt (maxLocalTime ω n) - timeCenter n|
  change K + 1 < |Real.sqrt (inclusiveMaxLocalTime ω n) - timeCenter n| at hω
  have hs := sqrt_inclusive_bounds ω n
  by_contra h
  have ha := abs_le.mp (le_of_not_gt h)
  have hi : |Real.sqrt (inclusiveMaxLocalTime ω n) - timeCenter n| ≤ K + 1 :=
    abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  exact (not_lt_of_ge hi) hω

end SRWTightness
