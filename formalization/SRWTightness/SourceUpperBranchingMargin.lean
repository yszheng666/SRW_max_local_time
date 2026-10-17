import SRWTightness.SourceUpperBranchingBarrier

namespace SRWTightness

/-- The terminal slack S(q) in source equation (4.26). -/
noncomputable def sourceUpperBranchingSlack (t s u : ℝ) : ℝ :=
  1 + sourceUpperBranchingEnd t s - u

/-- The endpoint margin equals the manuscript slack with q equal to target minus window height. -/
theorem sourceUpperBranchingSlack_eq (t s u : ℝ) :
    sourceUpperBranchingSlack t s u = 1 + (4 + s) +
      2 * upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) +
        (sourceUpperTarget t s - u) := by
  unfold sourceUpperBranchingSlack sourceUpperBranchingEnd
  ring

/-- The initial endpoint margin is uniformly linear in the excess height and root level. -/
theorem source_upper_branching_margin (t s x : ℝ) (k : ℕ) (hs : 0 ≤ s)
    (hθ : 0 ≤ sourceUpperSlope t s) (hθ3 : sourceUpperSlope t s ≤ 3) :
    0 ≤ 1 + sourceUpperBranchingStart t s k x - x ∧
      1 + sourceUpperBranchingStart t s k x - x ≤ 7 * (5 + s + k) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hp : (k : ℝ) ^ (1 / 4 : ℝ) ≤ k + 1 := by
    by_cases hz : k = 0
    · subst k
      norm_num
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hh := Real.rpow_le_self_of_one_le hk1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
      linarith
  have hpow := Real.rpow_nonneg hk (1 / 4 : ℝ)
  have hmul := mul_nonneg hθ hk
  have hmul3 := mul_le_mul_of_nonneg_right hθ3 hk
  unfold sourceUpperBranchingStart
  constructor <;> linarith

end SRWTightness
