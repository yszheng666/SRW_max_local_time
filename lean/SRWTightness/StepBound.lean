import SRWTightness.Geometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace SRWTightness

 theorem normSq_nonneg (x : Site) : 0 ≤ normSq x :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Every one-step overshoot of the radius-R disk has norm at most R+1. -/
theorem normSq_step_le (x : Site) (d : Direction) {R : ℝ} (hR : 0 ≤ R)
    (hx : normSq x ≤ R ^ 2) : normSq (x + step d) ≤ (R + 1) ^ 2 := by
  have h₁ : (x.1 : ℝ) ^ 2 ≤ R ^ 2 := by
    dsimp [normSq] at hx
    nlinarith [sq_nonneg (x.2 : ℝ)]
  have h₂ : (x.2 : ℝ) ^ 2 ≤ R ^ 2 := by
    dsimp [normSq] at hx
    nlinarith [sq_nonneg (x.1 : ℝ)]
  obtain ⟨hl₁, hu₁⟩ := abs_le_of_sq_le_sq' h₁ hR
  obtain ⟨hl₂, hu₂⟩ := abs_le_of_sq_le_sq' h₂ hR
  fin_cases d <;> simp [step, normSq] at * <;> nlinarith

/-- Deterministic finite-horizon bound for the actual SRW path. -/
theorem normSq_position_le (ω : Sample) (n : ℕ) :
    normSq (position ω n) ≤ (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp [position, normSq]
  | succ n ih =>
    simpa only [position, Nat.cast_add, Nat.cast_one] using
      normSq_step_le (position ω n) (ω n) (Nat.cast_nonneg n) ih

end SRWTightness
